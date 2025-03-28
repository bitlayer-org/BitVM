use crate::autochunker::intermediate_state::State;
use crate::autochunker::primitve_functions::ComputeFn;
use graphrs::readwrite;
use graphrs::{Edge, Graph, Node};
use std::sync::Arc;

#[derive(Clone)]
pub struct NodeInfo {
    // other information about graph, such as script, witness, template, etc.
    #[allow(unused)]
    pub script_size: usize,
    pub state: State,
    #[allow(unused)]
    pub function: ComputeFn,
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
    };
    let node = BitVMNode::new_node(name, node_info);
    graph.write().unwrap().add_node(node.clone());
    node
}

pub fn new_script<'a>(
    graph: &mut BitVMGraph,
    name: String,
    script_size: usize,
    compute_fn: ComputeFn,
    state: State,
    inputs: Vec<&BitVMNode>,
) -> BitVMNode {
    let node_info = NodeInfo {
        script_size,
        state: state.clone(),
        function: compute_fn,
    };
    let node = BitVMNode::new_node(name.clone(), node_info);
    graph.write().unwrap().add_node(node.clone());
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
            .write()
            .unwrap()
            .add_edge(edge)
            .expect(format!("fail to add edge: {} --> {}", input.name, name.clone()).as_str());
    }
    node
}

/// BitVM Graph
use std::sync::RwLock;
pub type BitVMGraph = Arc<RwLock<Graph<String, NodeInfo>>>;

pub struct GraphContext {
    pub graph: BitVMGraph,
    pub variable_prefix: String,
}

impl GraphContext {
    pub fn new(variable_prefix: &str) -> Self {
        let graph: Graph<String, NodeInfo> = Graph::new(graphrs::GraphSpecs::directed());
        GraphContext {
            graph: Arc::new(RwLock::new(graph)),
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
        readwrite::graphml::write_graphml_file(&self.graph.read().unwrap(), path)
    }
}
