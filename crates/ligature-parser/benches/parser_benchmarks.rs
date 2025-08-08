use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use ligature_ast::AstResult;
use ligature_parser::parse_expression;

/// Benchmark data for different types of expressions
struct BenchmarkData {
    name: &'static str,
    input: &'static str,
    category: &'static str,
}

/// Collection of benchmark test cases
fn benchmark_cases() -> Vec<BenchmarkData> {
    vec![
        // Simple literals
        BenchmarkData {
            name: "integer_literal",
            input: "42",
            category: "literals",
        },
        BenchmarkData {
            name: "float_literal",
            input: "3.14159",
            category: "literals",
        },
        BenchmarkData {
            name: "string_literal",
            input: "\"hello world\"",
            category: "literals",
        },
        BenchmarkData {
            name: "boolean_literal",
            input: "true",
            category: "literals",
        },
        // Arithmetic expressions
        BenchmarkData {
            name: "simple_addition",
            input: "1 + 2",
            category: "arithmetic",
        },
        BenchmarkData {
            name: "complex_arithmetic",
            input: "1 + 2 * 3 - 4 / 2",
            category: "arithmetic",
        },
        BenchmarkData {
            name: "parenthesized_arithmetic",
            input: "(1 + 2) * (3 - 4)",
            category: "arithmetic",
        },
        // Comparison expressions
        BenchmarkData {
            name: "simple_comparison",
            input: "x > 10",
            category: "comparison",
        },
        BenchmarkData {
            name: "compound_comparison",
            input: "x >= 10 && y <= 20",
            category: "comparison",
        },
        // Logical expressions
        BenchmarkData {
            name: "simple_logical",
            input: "true && false",
            category: "logical",
        },
        BenchmarkData {
            name: "complex_logical",
            input: "a && b || c && !d",
            category: "logical",
        },
        // Let expressions
        BenchmarkData {
            name: "simple_let",
            input: "let x = 42 in x",
            category: "let",
        },
        BenchmarkData {
            name: "nested_let",
            input: "let x = 1 in let y = 2 in x + y",
            category: "let",
        },
        // Function calls
        BenchmarkData {
            name: "simple_function_call",
            input: "f(x)",
            category: "function",
        },
        BenchmarkData {
            name: "nested_function_calls",
            input: "f(g(h(x)))",
            category: "function",
        },
        // Records
        BenchmarkData {
            name: "simple_record",
            input: "{ x: 1, y: 2 }",
            category: "record",
        },
        BenchmarkData {
            name: "nested_record",
            input: "{ x: { a: 1, b: 2 }, y: 3 }",
            category: "record",
        },
        // Lists
        BenchmarkData {
            name: "simple_list",
            input: "[1, 2, 3]",
            category: "list",
        },
        BenchmarkData {
            name: "nested_list",
            input: "[[1, 2], [3, 4], [5, 6]]",
            category: "list",
        },
        // Complex expressions
        BenchmarkData {
            name: "complex_expression",
            input: "let x = { a: 1, b: [2, 3] } in x.a + x.b[0]",
            category: "complex",
        },
        BenchmarkData {
            name: "very_complex_expression",
            input: "let config = { threshold: 100, enabled: true } in if config.enabled && value \
                    > config.threshold then process(value) else skip()",
            category: "complex",
        },
    ]
}

/// Benchmark parsing performance for different expression types
fn bench_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("parser");

    for case in benchmark_cases() {
        group.throughput(Throughput::Bytes(case.input.len() as u64));

        group.bench_with_input(
            BenchmarkId::new(case.category, case.name),
            &case.input,
            |b, input| {
                b.iter(|| {
                    let _result: AstResult<_> = parse_expression(input);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark parsing with error handling
fn bench_parser_with_errors(c: &mut Criterion) {
    let mut group = c.benchmark_group("parser_errors");

    let error_cases = vec![
        ("unclosed_paren", "(1 + 2"),
        ("unclosed_brace", "{ x: 1"),
        ("unclosed_bracket", "[1, 2"),
        ("invalid_syntax", "1 + + 2"),
        ("missing_operator", "1 2"),
    ];

    for (name, input) in error_cases {
        group.throughput(Throughput::Bytes(input.len() as u64));

        group.bench_with_input(
            BenchmarkId::new("error_handling", name),
            &input,
            |b, input| {
                b.iter(|| {
                    let _result: AstResult<_> = parse_expression(input);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark parsing large expressions
fn bench_large_expressions(c: &mut Criterion) {
    let mut group = c.benchmark_group("large_expressions");

    // Generate large expressions
    let large_arithmetic = (1..100)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(" + ");
    let large_list = format!(
        "[{}]",
        (1..100)
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    let large_record = format!(
        "{{{}}}",
        (1..50)
            .map(|i| format!("x{i}: {i}"))
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
                let _result: AstResult<_> = parse_expression(input);
            });
        });
    }

    group.finish();
}

/// Benchmark memory usage during parsing
fn bench_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");

    // Use a complex expression that might stress memory allocation
    let complex_expr =
        "let x = { a: 1, b: [2, 3, 4, 5], c: { d: 6, e: 7 } } in x.a + x.b[0] * x.c.d";

    group.bench_with_input(
        BenchmarkId::new("memory", "complex_expression"),
        &complex_expr,
        |b, input| {
            b.iter(|| {
                let _result: AstResult<_> = parse_expression(input);
            });
        },
    );

    group.finish();
}

criterion_group!(
    benches,
    bench_parser,
    bench_parser_with_errors,
    bench_large_expressions,
    bench_memory_usage
);
criterion_main!(benches);
