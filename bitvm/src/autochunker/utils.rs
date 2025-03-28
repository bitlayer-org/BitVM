use crate::computation_graph::*;

/// three input each which is fq2
pub fn new_square_fq6(
    graph: &mut BitVMGraph,
    format_name: String,
    inputs: [&BitVMNode; 3],
) -> [BitVMNode; 3] {
    let (a0, a1, a2) = (inputs[0], inputs[1], inputs[2]);

    let s0 = new_script(
        graph,
        format!("{}_s0", format_name),
        137000,
        vec![(&a0, FQ2_BYTES)],
    );

    // s1 = (a_0 + a_1 + a_2)^2
    let s1 = new_script(
        graph,
        format!("{}_s1", format_name),
        137000,
        vec![(&a0, FQ2_BYTES), (&a1, FQ2_BYTES), (&a2, FQ2_BYTES)],
    );

    // s2 = (a_0 - a_1 + a_2)^2
    let s2 = new_script(
        graph,
        format!("{}_s2", format_name),
        137000,
        vec![(&a0, FQ2_BYTES), (&a1, FQ2_BYTES), (&a2, FQ2_BYTES)],
    );

    // s3 = 2 \cdot a_1 \cdot a_2
    let s3 = new_script(
        graph,
        format!("{}_s3", format_name),
        137000,
        vec![(&a0, FQ2_BYTES), (&a1, FQ2_BYTES)],
    );

    // s4 = a_2^2
    let s4 = new_script(
        graph,
        format!("{}_s4", format_name),
        137000,
        vec![(&a2, FQ2_BYTES)],
    );

    // t4 = (s1 + s2) / 2
    let t4 = new_script(
        graph,
        format!("{}_t4", format_name),
        137000,
        vec![(&s1, FQ2_BYTES), (&s2, FQ2_BYTES)],
    );

    // c0 = s0 + \beta \cdot s_3
    let c0 = new_script(
        graph,
        format!("{}_c0", format_name),
        137000,
        vec![(&s0, FQ2_BYTES), (&s3, FQ2_BYTES)],
    );

    // c1 = s1 - s3 - t1 + \beta s4
    let c1 = new_script(
        graph,
        format!("{}_c1", format_name),
        137000,
        vec![
            (&s1, FQ2_BYTES),
            (&s3, FQ2_BYTES),
            (&s4, FQ2_BYTES),
            (&t4, FQ2_BYTES),
        ],
    );

    // c2 = t1 - s0 - s4
    let c2 = new_script(
        graph,
        format!("{}_c2", format_name),
        137000,
        vec![(&s0, FQ2_BYTES), (&s4, FQ2_BYTES), (&t4, FQ2_BYTES)],
    );

    [c0, c1, c2]
}
