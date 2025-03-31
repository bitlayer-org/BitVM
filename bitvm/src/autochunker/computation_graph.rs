use crate::autochunker::intermediate_state::State;
use crate::autochunker::primitve_functions::ComputeFn;
use core::borrow;
use graphrs::readwrite;
use graphrs::{Edge, Graph, Node};
use log::{debug, info, warn};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex};
use tqdm::refresh;

#[derive(Clone)]
pub struct NodeInfo {
    // other information about graph, such as script, witness, template, etc.
    #[allow(unused)]
    pub script_size: usize,
    pub state: State,
    #[allow(unused)]
    pub function: ComputeFn,
    pub predecessor: Vec<String>,
}

impl std::fmt::Debug for NodeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeInfo")
            .field("script_size", &self.script_size)
            .field("state", &self.state)
            .finish()
    }
}

/// A node with name and size (bytes) of Bitcoin script.
pub type BitVMNode = Arc<Node<String, NodeInfo>>;

pub trait BitVMNodeTrait {
    fn new_node(script_name: String, script_size: NodeInfo) -> BitVMNode;
}

impl BitVMNodeTrait for BitVMNode {
    fn new_node(script_name: String, info: NodeInfo) -> BitVMNode {
        Node::from_name_and_attributes(script_name, info)
    }
}

/// A edge with name and size (bytes) of intermeidate state.
pub type BitVMEdge = Arc<Edge<String, NodeInfo>>;

pub trait BitVMEdgeTrait {
    fn new_edge(from: String, to: String, cost: usize) -> BitVMEdge;
}

impl BitVMEdgeTrait for BitVMEdge {
    fn new_edge(from: String, to: String, cost: usize) -> BitVMEdge {
        let edge = Edge::with_weight(from, to, cost as f64);
        edge
    }
}

/// Create new input from outside (proof or scalars)
pub fn new_input(
    graph: &mut BitVMGraph,
    name: String,
    state: State,
    compute_fn: ComputeFn,
) -> BitVMNode {
    let node_info = NodeInfo {
        script_size: 0,
        state: state.clone(),
        function: compute_fn,
        predecessor: vec![],
    };
    let node = BitVMNode::new_node(name, node_info);
    graph.lock().unwrap().add_node(node.clone());
    node
}

pub fn new_script<'a>(
    graph: &mut BitVMGraph,
    name: String,
    script_size: usize,
    compute_fn: ComputeFn,
    state: State,
    inputs: Vec<BitVMNode>,
) -> BitVMNode {
    let predecessor: Vec<String> = inputs.iter().map(|x| x.name.to_string()).collect();
    let node_info = NodeInfo {
        script_size,
        state: state.clone(),
        function: compute_fn,
        predecessor,
    };
    let node = BitVMNode::new_node(name.clone(), node_info);
    graph.lock().unwrap().add_node(node.clone());
    for input in inputs {
        let edge = BitVMEdge::new_edge(
            input.name.clone(),
            name.clone(),
            input
                .attributes
                .as_ref()
                .unwrap()
                .state
                .bit_commitment_cost(),
        );
        graph
            .lock()
            .unwrap()
            .add_edge(edge)
            .expect(format!("fail to add edge: {} --> {}", input.name, name.clone()).as_str());
    }
    node
}

/// BitVM Graph
use super::primitve_functions::ComputeCtx;
pub type BitVMGraph = Arc<Mutex<Graph<String, NodeInfo>>>;

pub struct GraphContext {
    pub graph: BitVMGraph,
    pub variable_prefix: String,
}

impl GraphContext {
    pub fn new(variable_prefix: &str) -> Self {
        let graph: Graph<String, NodeInfo> = Graph::new(graphrs::GraphSpecs::directed());
        GraphContext {
            graph: Arc::new(Mutex::new(graph)),
            variable_prefix: variable_prefix.to_string(),
        }
    }

    pub fn inner_context(&self, prefix: &str) -> GraphContext {
        GraphContext {
            graph: self.graph.clone(),
            variable_prefix: format!("{}{}", self.variable_prefix.clone(), prefix),
        }
    }

    pub fn write_local(&self, path: &str) -> std::io::Result<()> {
        let graph = self.graph.lock().unwrap();
        readwrite::graphml::write_graphml_file(&graph, path)
    }
}

pub fn compute_states(graph_ctx: &GraphContext, ctx: ComputeCtx) {
    let inputs: Vec<String> = {
        let graph = graph_ctx.graph.lock().unwrap();

        graph
            .get_all_node_names()
            .into_iter()
            .filter(|x| graph.get_node_in_degree(x.to_string()).unwrap() == 0)
            .map(|x| x.to_string())
            .collect()
    };

    info!("inputs: {:?}", inputs);

    let mut queue_x: VecDeque<String> = VecDeque::from(inputs.clone());
    let mut set_x: HashSet<String> = HashSet::from_iter(inputs.into_iter());
    let mut set_y: HashSet<String> = HashSet::new();
    let mut set_y_count = 0;

    #[allow(while_true)]
    'main: while true {
        // no element in set x left
        let x = match queue_x.pop_front() {
            Some(x) => x,
            None => {
                break;
            }
        };
        set_x.remove(&x);

        debug!("handle {}, set_x: {:?}", x, queue_x);

        let mut cur_node_info = {
            let graph = graph_ctx.graph.lock().unwrap();
            // extract function from node
            let node = graph.get_node(x.clone()).unwrap();
            node.attributes.as_ref().unwrap().clone()
        };

        let mut predecessor_states: Vec<State> = vec![];
        {
            let graph = graph_ctx.graph.lock().unwrap();
            for name in cur_node_info.predecessor.iter() {
                let state = graph
                    .get_node(name.to_string())
                    .unwrap()
                    .attributes
                    .as_ref()
                    .unwrap()
                    .state
                    .clone();
                // if some states are not filled, put it to the end of queue
                if !state.is_filled() {
                    // set_x.push_back(x.clone());
                    warn!(
                        "the predecessor {} of {} are not all filled, drop it",
                        name, x
                    );
                    continue 'main;
                }
                debug!("predecessor of {} captured", x);
                predecessor_states.push(state);
            }
        }

        // execute function
        let result_state = (cur_node_info.function)(ctx.clone(), predecessor_states);

        // update attributes
        assert_eq!(
            cur_node_info.state.get_type_name(),
            result_state.get_type_name()
        );
        cur_node_info.state = result_state;

        // prepare new node outside of mutable borrow
        let new_node = BitVMNode::new_node(x.to_string(), cur_node_info);

        // update node in graph
        {
            let mut graph = graph_ctx.graph.lock().unwrap();
            graph.add_node(new_node);
        }

        set_y.insert(x.to_string());
        set_y_count += 1;

        // add successors to the front of queue
        {
            let graph = graph_ctx.graph.lock().unwrap();
            graph
                .get_successor_node_names(x.to_string())
                .unwrap()
                .into_iter()
                .rev()
                .for_each(|x| {
                    if !set_x.contains(x) && !set_y.contains(x) {
                        queue_x.push_front(x.to_string());
                        set_x.insert(x.to_string());
                    }
                });
        }
    }

    let graph = graph_ctx.graph.lock().unwrap();
    info!(
        "finished states / total states = {} / {}",
        set_y_count,
        graph.number_of_nodes(),
    );
}
