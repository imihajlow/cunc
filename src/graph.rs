use std::cmp;
use std::collections::HashMap;

pub struct Graph {
    edges: Vec<Vec<usize>>,
}

impl Graph {
    pub fn new() -> Self {
        Self {
            edges: Vec::new(),
        }
    }

    pub fn add_nodes_up_to(&mut self, n: usize) {
        if n >= self.edges.len() {
            self.edges.resize(n + 1, Vec::new());
        }
    }

    pub fn add_edge(&mut self, from: usize, to: usize) {
        self.add_nodes_up_to(from);
        self.add_nodes_up_to(to);

        self.edges[from].push(to);
    }

    pub fn add_edge_unique(&mut self, from: usize, to: usize) {
        self.add_nodes_up_to(from);
        self.add_nodes_up_to(to);
        if !self.edges[from].contains(&to) {
            self.edges[from].push(to);
        }
    }

    pub fn get_node_count(&self) -> usize {
        self.edges.len()
    } 

    pub fn has_edge(&self, from: usize, to: usize) -> bool {
        self.edges[from].contains(&to)
    }

    /// Find strongly connected components.
    ///
    /// Returns the graph of components and a mapping from the nodes of the original graph
    /// to the nodes of the SCC graph.
    pub fn find_strongly_connected(&self) -> (Graph, Vec<usize>) {
        // https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
        let mut stack: Vec<usize> = Vec::new();
        let mut indices: Vec<Option<usize>> = vec![None; self.edges.len()];
        let mut lowlink: Vec<usize> = vec![0; self.edges.len()];
        let mut onstack: Vec<bool> = vec![false; self.edges.len()];
        let mut index: usize = 0;
        let mut result: Vec<Vec<usize>> = Vec::new();

        fn strongconnect(v: usize,
            edges: &Vec<Vec<usize>>,
            indices: &mut Vec<Option<usize>>,
            lowlink: &mut Vec<usize>,
            stack: &mut Vec<usize>,
            onstack: &mut Vec<bool>,
            index: &mut usize,
            result: &mut Vec<Vec<usize>>) {
            indices[v] = Some(*index);
            lowlink[v] = *index;
            *index += 1;
            stack.push(v);
            onstack[v] = true;
            for w in edges[v].iter() {
                if indices[*w].is_none() {
                    strongconnect(*w, edges, indices, lowlink, stack, onstack, index, result);
                    lowlink[v] = cmp::min(lowlink[v], lowlink[*w]);
                } else {
                    // Successor w is in stack and hence in the current SCC
                    // If w is not on stack, then (v, w) is an edge pointing to an SCC already found and must be ignored
                    lowlink[v] = cmp::min(lowlink[v], indices[*w].unwrap());
                }
            }
            // If v is a root node, pop the stack and generate an SCC
            if lowlink[v] == indices[v].unwrap() {
                let mut r: Vec<usize> = Vec::new();
                loop {
                    let w = stack.pop().unwrap();
                    onstack[w] = false;
                    r.push(w);

                    if w == v {
                        break;
                    }
                }
                result.push(r);
            }
        }

        for i in 0..self.edges.len() {
            if indices[i].is_none() {
                strongconnect(i, &self.edges, &mut indices, &mut lowlink, &mut stack, &mut onstack, &mut index, &mut result);
            }
        }
        let mut v_to_scc: Vec<usize> = vec![0; self.edges.len()];
        for (i, scc) in result.iter().enumerate() {
            for v in scc {
                v_to_scc[*v] = i;
            }
        }
        let mut result_graph = Graph::new();
        for v in 0..self.edges.len() {
            let v_scc = v_to_scc[v];
            for w in self.edges[v].iter() {
                let w_scc = v_to_scc[*w];
                if v_scc != w_scc {
                    result_graph.add_edge_unique(v_scc, w_scc);
                }
            }
        }
        (result_graph, v_to_scc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scc() {
        let mut g = Graph::new();
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        g.add_edge(3, 4);
        g.add_edge(4, 0);
        g.add_edge(6, 7);
        g.add_edge(6, 8);
        let (scc, m) = g.find_strongly_connected();
        assert_eq!(scc.get_node_count(), 5);
        assert_eq!(m[0], m[1]);
        assert_eq!(m[0], m[2]);
        assert_eq!(m[0], m[3]);
        assert_eq!(m[0], m[4]);
        assert_ne!(m[5], m[0]);
        assert_ne!(m[5], m[6]);
        assert_ne!(m[5], m[7]);
        assert_ne!(m[5], m[8]);
        assert_ne!(m[6], m[0]);
        assert_ne!(m[6], m[7]);
        assert_ne!(m[6], m[8]);
        assert_ne!(m[7], m[0]);
        assert_ne!(m[7], m[8]);
        assert_ne!(m[8], m[0]);
        assert!(!scc.has_edge(m[0], m[0]));
        assert!(!scc.has_edge(m[5], m[5]));
        assert!(!scc.has_edge(m[7], m[7]));
        assert!(!scc.has_edge(m[6], m[6]));
        assert!(!scc.has_edge(m[8], m[8]));
        assert!(scc.has_edge(m[6], m[7]));
        assert!(scc.has_edge(m[6], m[8]));
    }
}
