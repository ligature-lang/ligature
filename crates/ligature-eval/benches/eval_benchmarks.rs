use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use ligature_ast::AstResult;
use ligature_eval::Value;
use ligature_eval::evaluate_expression;
use ligature_parser::parse_expression;

/// Benchmark data for different types of expressions
struct EvalBenchmarkData {
    name: &'static str,
    input: &'static str,
    category: &'static str,
}

/// Collection of evaluation benchmark test cases
fn eval_benchmark_cases() -> Vec<EvalBenchmarkData> {
    vec![
        // Simple literals
        EvalBenchmarkData {
            name: "integer_literal",
            input: "42",
            category: "literals",
        },
        EvalBenchmarkData {
            name: "float_literal",
            input: "3.14159",
            category: "literals",
        },
        EvalBenchmarkData {
            name: "string_literal",
            input: "\"hello world\"",
            category: "literals",
        },
        EvalBenchmarkData {
            name: "boolean_literal",
            input: "true",
            category: "literals",
        },
        // Arithmetic expressions
        EvalBenchmarkData {
            name: "simple_addition",
            input: "1 + 2",
            category: "arithmetic",
        },
        EvalBenchmarkData {
            name: "complex_arithmetic",
            input: "1 + 2 * 3 - 4 / 2",
            category: "arithmetic",
        },
        EvalBenchmarkData {
            name: "parenthesized_arithmetic",
            input: "(1 + 2) * (3 - 4)",
            category: "arithmetic",
        },
        EvalBenchmarkData {
            name: "floating_point_arithmetic",
            input: "3.14 * 2.0 + 1.5",
            category: "arithmetic",
        },
        // Comparison expressions
        EvalBenchmarkData {
            name: "simple_comparison",
            input: "10 > 5",
            category: "comparison",
        },
        EvalBenchmarkData {
            name: "compound_comparison",
            input: "10 >= 5 && 20 <= 30",
            category: "comparison",
        },
        EvalBenchmarkData {
            name: "equality_comparison",
            input: "42 == 42 && 3.14 != 2.71",
            category: "comparison",
        },
        // Logical expressions
        EvalBenchmarkData {
            name: "simple_logical",
            input: "true && false",
            category: "logical",
        },
        EvalBenchmarkData {
            name: "complex_logical",
            input: "true && true || false && !false",
            category: "logical",
        },
        EvalBenchmarkData {
            name: "short_circuit_logical",
            input: "false && (1 / 0 == 0)",
            category: "logical",
        },
        // Let expressions
        EvalBenchmarkData {
            name: "simple_let",
            input: "let x = 42 in x",
            category: "let",
        },
        EvalBenchmarkData {
            name: "nested_let",
            input: "let x = 1 in let y = 2 in x + y",
            category: "let",
        },
        EvalBenchmarkData {
            name: "let_with_complex_expression",
            input: "let x = 1 + 2 * 3 in let y = x * 2 in y + 1",
            category: "let",
        },
        // Conditional expressions
        EvalBenchmarkData {
            name: "simple_if",
            input: "if true then 1 else 2",
            category: "conditional",
        },
        EvalBenchmarkData {
            name: "nested_if",
            input: "if 10 > 5 then if 3 < 2 then 1 else 2 else 3",
            category: "conditional",
        },
        EvalBenchmarkData {
            name: "if_with_complex_condition",
            input: "if (1 + 2) * 3 > 10 then 42 else 0",
            category: "conditional",
        },
        // Records
        EvalBenchmarkData {
            name: "simple_record",
            input: "{ x: 1, y: 2 }",
            category: "record",
        },
        EvalBenchmarkData {
            name: "record_access",
            input: "let r = { x: 1, y: 2 } in r.x + r.y",
            category: "record",
        },
        EvalBenchmarkData {
            name: "nested_record",
            input: "let r = { x: { a: 1, b: 2 }, y: 3 } in r.x.a + r.y",
            category: "record",
        },
        // Lists
        EvalBenchmarkData {
            name: "simple_list",
            input: "[1, 2, 3]",
            category: "list",
        },
        EvalBenchmarkData {
            name: "list_access",
            input: "let l = [1, 2, 3, 4, 5] in l[0] + l[1]",
            category: "list",
        },
        EvalBenchmarkData {
            name: "nested_list",
            input: "let l = [[1, 2], [3, 4], [5, 6]] in l[0][0] + l[1][1]",
            category: "list",
        },
        // Complex expressions
        EvalBenchmarkData {
            name: "complex_expression",
            input: "let x = { a: 1, b: [2, 3] } in x.a + x.b[0]",
            category: "complex",
        },
        EvalBenchmarkData {
            name: "very_complex_expression",
            input: "let config = { threshold: 100, enabled: true } in if config.enabled && 150 > config.threshold then 42 else 0",
            category: "complex",
        },
        EvalBenchmarkData {
            name: "mathematical_expression",
            input: "let x = 10 in let y = 20 in (x + y) * (x - y) / 2",
            category: "complex",
        },
    ]
}

/// Benchmark evaluation performance for different expression types
fn bench_evaluator(c: &mut Criterion) {
    let mut group = c.benchmark_group("evaluator");

    for case in eval_benchmark_cases() {
        group.throughput(Throughput::Bytes(case.input.len() as u64));

        group.bench_with_input(
            BenchmarkId::new(case.category, case.name),
            &case.input,
            |b, input| {
                b.iter(|| {
                    let _result: AstResult<Value> =
                        parse_expression(input).and_then(|expr| evaluate_expression(&expr));
                });
            },
        );
    }

    group.finish();
}

/// Benchmark evaluation with error handling
fn bench_evaluator_with_errors(c: &mut Criterion) {
    let mut group = c.benchmark_group("evaluator_errors");

    let error_cases = vec![
        ("division_by_zero", "1 / 0"),
        ("invalid_list_access", "[1, 2, 3][10]"),
        ("invalid_record_access", "let r = { x: 1 } in r.y"),
        ("type_mismatch", "1 + \"hello\""),
        ("undefined_variable", "undefined_var"),
    ];

    for (name, input) in error_cases {
        group.throughput(Throughput::Bytes(input.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("error_handling", name),
            &input,
            |b, input| {
                b.iter(|| {
                    let _result: AstResult<Value> =
                        parse_expression(input).and_then(|expr| evaluate_expression(&expr));
                });
            },
        );
    }

    group.finish();
}

/// Benchmark evaluation of large expressions
fn bench_large_eval_expressions(c: &mut Criterion) {
    let mut group = c.benchmark_group("large_eval_expressions");

    // Generate large expressions
    let large_arithmetic = (1..50)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(" + ");
    let large_list = format!(
        "[{}]",
        (1..50)
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    let large_record = format!(
        "{{{}}}",
        (1..25)
            .map(|i| format!("x{}: {}", i, i))
            .collect::<Vec<_>>()
            .join(", ")
    );

    let large_cases = vec![
        ("large_arithmetic", &large_arithmetic),
        ("large_list", &large_list),
        ("large_record", &large_record),
    ];

    for (name, input) in large_cases {
        group.throughput(Throughput::Bytes(input.len() as u64));

        group.bench_with_input(BenchmarkId::new("large", name), &input, |b, input| {
            b.iter(|| {
                let _result: AstResult<Value> =
                    parse_expression(input).and_then(|expr| evaluate_expression(&expr));
            });
        });
    }

    group.finish();
}

/// Benchmark memory usage during evaluation
fn bench_eval_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("eval_memory_usage");

    // Use a complex expression that might stress memory allocation
    let complex_expr =
        "let x = { a: 1, b: [2, 3, 4, 5], c: { d: 6, e: 7 } } in x.a + x.b[0] * x.c.d";

    group.bench_with_input(
        BenchmarkId::new("memory", "complex_expression"),
        &complex_expr,
        |b, input| {
            b.iter(|| {
                let _result: AstResult<Value> =
                    parse_expression(input).and_then(|expr| evaluate_expression(&expr));
            });
        },
    );

    group.finish();
}

/// Benchmark end-to-end parsing and evaluation
fn bench_end_to_end(c: &mut Criterion) {
    let mut group = c.benchmark_group("end_to_end");

    let end_to_end_cases = vec![
        (
            "simple_config",
            "let config = { port: 8080, host: \"localhost\" } in config.port",
        ),
        (
            "conditional_config",
            "let env = \"production\" in if env == \"production\" then { debug: false, port: 443 } else { debug: true, port: 3000 }",
        ),
        (
            "nested_config",
            "let base = { timeout: 30 } in let extended = { base, retries: 3 } in extended.timeout * extended.retries",
        ),
    ];

    for (name, input) in end_to_end_cases {
        group.throughput(Throughput::Bytes(input.len() as u64));

        group.bench_with_input(BenchmarkId::new("end_to_end", name), &input, |b, input| {
            b.iter(|| {
                let _result: AstResult<Value> =
                    parse_expression(input).and_then(|expr| evaluate_expression(&expr));
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_evaluator,
    bench_evaluator_with_errors,
    bench_large_eval_expressions,
    bench_eval_memory_usage,
    bench_end_to_end
);
criterion_main!(benches);
