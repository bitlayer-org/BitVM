use super::intermediate_state::execute_info_to_witness;
use super::primitve_functions::placeholder_script_fn;
use crate::autochunker::compute_ctx::ComputeFn;
use crate::autochunker::intermediate_state::State;
use crate::execute_script_with_inputs;
use bitcoin::hashes::hash160::Hash;
use bitcoin::witness;
use core::borrow;
use graphrs::readwrite;
use graphrs::{Edge, Graph, Node};
use log::{debug, info, warn};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex};
use tqdm::refresh;
pub type BitVMGraph = Arc<Mutex<Graph<String, NodeInfo>>>;
use super::compute_ctx::{ComputeCtx, ScriptFn};

// Define the `define_script` macro
#[macro_export]
macro_rules! define_input {
    ($context:ident, $name:tt, $state_type:ident, $func:expr) => {
        paste::paste! {
            let state = State::[<new_ $state_type:lower>]();
            let var_name = $context.new_var(stringify!($name));
            let $name = new_input(&mut $context.graph, var_name, state, $func);
        }
    };
}

#[macro_export]
macro_rules! define_script {
    // name hasn't been defined
    ($context: ident, $name: ident, $state_type:ident, [$($input:ident),*], $func:expr) => {
        let function = $func.0;
        let script_size = $func.1;
        let var_name = $context.new_var(stringify!($name));
        let mut inputs = vec![];
        $(inputs.push($input.clone());)*
        paste::paste!{
            let state = State::[<new_ $state_type:lower>]();
            let $name = new_script(
                &mut $context.graph,
                var_name,
                script_size,
                function,
                state,
                inputs,
            );
        }
    };
}

#[macro_export]
macro_rules! define_overide_script {
    // name has been defined and override
    ($context: ident, $name: ident, $state_type:ident, [$($input:ident),*], $func:expr) => {
        let (function, script_size) = $func;
        let var_name = $context.new_var(stringify!($name));
        let mut inputs = vec![];
        $(inputs.push($input.clone());)*
        paste::paste!{
            let state = State::[<new_ $state_type:lower>]();
            $name = new_script(
                &mut $context.graph,
                var_name,
                script_size,
                function,
                state,
                inputs,
            );
        }
    };
}

#[derive(Clone)]
pub struct NodeInfo {
    // other information about graph, such as script, witness, template, etc.
    #[allow(unused)]
    pub script_fn: Arc<ScriptFn>,
    pub state: State,
    #[allow(unused)]
    pub function: Arc<ComputeFn>,
    pub predecessor: Vec<String>,
    // cached scripts' info, either load from cache or generate from `script_fn`
    pub cached_script: Option<ScriptCache>,
}

#[derive(Clone)]
struct ScriptCache {
    script_len: usize,   // total bytes of script
    witness_size: usize, // total bytes of witness
    script: Vec<u8>,     // script bytes
}

impl std::fmt::Debug for NodeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeInfo")
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
        script_fn: Arc::new(placeholder_script_fn()),
        state: state.clone(),
        function: Arc::new(compute_fn),
        predecessor: vec![],
        cached_script: None,
    };
    let node = BitVMNode::new_node(name, node_info);
    graph.lock().unwrap().add_node(node.clone());
    node
}

pub fn new_script<'a>(
    graph: &mut BitVMGraph,
    name: String,
    script_fn: ScriptFn,
    compute_fn: ComputeFn,
    state: State,
    inputs: Vec<BitVMNode>,
) -> BitVMNode {
    let predecessor: Vec<String> = inputs.iter().map(|x| x.name.to_string()).collect();
    let node_info = NodeInfo {
        script_fn: Arc::new(script_fn),
        state: state.clone(),
        function: Arc::new(compute_fn),
        predecessor,
        cached_script: None,
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

pub struct GraphContext {
    pub graph: BitVMGraph,
    pub variable_prefix: String,
    pub node_name_set: Arc<Mutex<HashSet<String>>>,
}

impl GraphContext {
    pub fn new(variable_prefix: &str) -> Self {
        let graph: Graph<String, NodeInfo> = Graph::new(graphrs::GraphSpecs::directed());
        GraphContext {
            graph: Arc::new(Mutex::new(graph)),
            variable_prefix: variable_prefix.to_string(),
            node_name_set: Arc::new(HashSet::new().into()),
        }
    }

    pub fn inner_context(&self, prefix: &str) -> GraphContext {
        GraphContext {
            graph: self.graph.clone(),
            variable_prefix: format!("{}_{}", self.variable_prefix.clone(), prefix),
            node_name_set: self.node_name_set.clone(),
        }
    }

    pub fn write_local(&self, path: &str) -> std::io::Result<()> {
        let graph = self.graph.lock().unwrap();
        readwrite::graphml::write_graphml_file(&graph, path)
    }

    pub fn new_var(&mut self, name: &str) -> String {
        let new_var_name = format!("{}_{}", self.variable_prefix.clone(), name);
        if self.node_name_set.lock().unwrap().contains(&new_var_name) {
            panic!("variable {} already exists", new_var_name);
        }
        self.node_name_set
            .lock()
            .unwrap()
            .insert(new_var_name.clone());
        new_var_name
    }

    pub fn get_node_info(&self, name: &str) -> NodeInfo {
        let graph = self.graph.lock().unwrap();
        let node = graph.get_node(name.to_string()).unwrap();
        node.attributes.as_ref().unwrap().clone()
    }

    pub fn get_state(&self, name: &str) -> State { self.get_node_info(name).state }

    pub fn all_inputs(&self) -> Vec<String> {
        let graph = self.graph.lock().unwrap();
        graph
            .get_all_node_names()
            .into_iter()
            .filter(|x| graph.get_node_in_degree(x.to_string()).unwrap() == 0)
            .map(|x| x.to_string())
            .collect()
    }

    pub fn get_all_nodes_name(&self) -> Vec<String> {
        let graph = self.graph.lock().unwrap();
        graph
            .get_all_node_names()
            .into_iter()
            .map(|x| x.to_string())
            .collect()
    }
}

// return all states that have been computed
pub fn compute_states(graph_ctx: &GraphContext, ctx: &ComputeCtx) -> usize {
    let inputs: Vec<String> = graph_ctx.all_inputs();
    debug!("inputs: {:?}", inputs);

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

        let (mut cur_node_info, name) = {
            let graph = graph_ctx.graph.lock().unwrap();
            // extract function from node
            let node = graph.get_node(x.clone()).unwrap();
            (node.attributes.as_ref().unwrap().clone(), node.name.clone())
        };

        let mut predecessor_states: Vec<State> = vec![];
        {
            for name in cur_node_info.predecessor.iter() {
                let state = graph_ctx.get_state(name);
                // if some states are not filled, put it to the end of queue
                if !state.is_filled() {
                    // set_x.push_back(x.clone());
                    debug!(
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
        let result_state = (cur_node_info.function)(ctx, predecessor_states);

        // update attributes
        assert_eq!(
            cur_node_info.state.get_type_name(),
            result_state.get_type_name(),
            "cur_node_info: {}",
            &name
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
    set_y_count
}

pub fn check_all_scripts(graph_ctx: &GraphContext, ctx: &ComputeCtx) {
    let inputs: Vec<String> = graph_ctx.all_inputs();
    let all_node_name = graph_ctx.get_all_nodes_name();

    // remove inputs from all_node_name
    let node_names_check_list: Vec<String> = all_node_name
        .into_iter()
        .filter(|x| !inputs.contains(x))
        .collect();

    // will take around 2.5 minutes to finish
    for name in tqdm::tqdm(node_names_check_list.iter()).desc(Some("check all scripts")) {
        let node_info = graph_ctx.get_node_info(name);
        let states: Vec<_> = node_info
            .predecessor
            .iter()
            .map(|x| {
                let state = graph_ctx.get_state(x);
                if !state.is_filled() {
                    panic!("state {} is not filled", x);
                }
                state
            })
            .collect();

        let (script, witness) = (node_info.script_fn)(ctx, states.clone());

        let mut input = witness;
        for state in states.iter() {
            input.append(&mut state.to_witness())
        }
        let expect_output = node_info.state.to_witness();

        let exec_info = execute_script_with_inputs(script, input);
        let output = execute_info_to_witness(&exec_info);
        if output != expect_output {
            log::error!(
                "{} mismatch: {:?}, output: {:?}, expected: {:?}, expected_state: {:?}",
                name,
                exec_info,
                output,
                expect_output,
                node_info.state,
            );
        } else {
            log::debug!("{} passed", name);
        }

        /*
        TODO: cache it somewhare?
        let (script_len, witness_len) =
            (script.len(), witness.iter().fold(0, |sum, x| sum + x.len()));
        let script_bytes = script.compile().to_bytes();
        let script_cache = ScriptCache {
            script_len,
            witness_size: witness_len,
            script: script_bytes,
        };

        // update state
        node_info.cached_script = Some(script_cache);
        */

        // prepare new node outside of mutable borrow
        let new_node = BitVMNode::new_node(name.to_string(), node_info);
        graph_ctx.graph.lock().unwrap().add_node(new_node);
    }
}

pub fn load_script_cache_from_file() {
    todo! {}
}

pub fn save_script_cache_to_file() {
    todo! {}
}

pub fn graph_partition(
    graph_ctx: &GraphContext,
    ctx: &ComputeCtx,
) -> (Vec<BitVMGraph>, Vec<BitVMGraph>) {
    let inputs: Vec<String> = graph_ctx.all_inputs();
    let all_node_name = graph_ctx.get_all_nodes_name();

    // remove inputs from all_node_name
    let node_names_check_list: Vec<String> = all_node_name
        .into_iter()
        .filter(|x| !inputs.contains(x))
        .collect();

    let mut all_scripts_bytes = 0;

    for name in tqdm::tqdm(node_names_check_list.iter()).desc(Some("check all scripts")) {
        let node_info = graph_ctx.get_node_info(name);
        let states: Vec<_> = node_info
            .predecessor
            .iter()
            .map(|x| {
                let state = graph_ctx.get_state(x);
                if !state.is_filled() {
                    panic!("state {} is not filled", x);
                }
                state
            })
            .collect();

        let (script, witness) = (node_info.script_fn)(ctx, states.clone());
        all_scripts_bytes += script.len();
    }
    info!("total script bytes: {}", all_scripts_bytes);

    todo!()
}
