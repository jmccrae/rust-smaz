//! Compares this crate with the original hash-map implementation
//! (smaz 0.1.0 on crates.io). Run with `cargo bench`.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

// The examples from the crate documentation: short strings, which smaz is
// designed for
const SHORT: [&str; 15] = [
    "This is a small string",
    "foobar",
    "the end",
    "not-a-g00d-Exampl333",
    "Smaz is a simple compression library",
    "Nothing is more difficult, and therefore more precious, than to be able to decide",
    "this is an example of what works very well with smaz",
    "1000 numbers 2000 will 10 20 30 compress very little",
    "and now a few italian sentences:",
    "Nel mezzo del cammin di nostra vita, mi ritrovai in una selva oscura",
    "Mi illumino di immenso",
    "L'autore di questa libreria vive in Sicilia",
    "try it against urls",
    "http://google.com",
    "http://programming.reddit.com",
];

const TEXT: &str = "It is a truth universally acknowledged, that a single man in \
possession of a good fortune, must be in want of a wife. However little known the \
feelings or views of such a man may be on his first entering a neighbourhood, this \
truth is so well fixed in the minds of the surrounding families, that he is \
considered the rightful property of some one or other of their daughters.";

const NON_ASCII: &str = "Tá an Ghaeilge ina teanga oifigiúil in Éirinn. \
日本語のテキストも圧縮できます。 Ünïcödé çhäràctérs — “quoted” 🎉";

fn inputs() -> Vec<(&'static str, Vec<Vec<u8>>)> {
    // Deterministic pseudo-random bytes
    let mut x: u64 = 42;
    let binary: Vec<u8> = (0..1024)
        .map(|_| {
            x = x
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (x >> 33) as u8
        })
        .collect();
    vec![
        (
            "short",
            SHORT.iter().map(|s| s.as_bytes().to_vec()).collect(),
        ),
        ("text", vec![TEXT.as_bytes().to_vec()]),
        ("non_ascii", vec![NON_ASCII.as_bytes().to_vec()]),
        ("binary", vec![binary]),
    ]
}

fn bench_compress(c: &mut Criterion) {
    let mut group = c.benchmark_group("compress");
    for (name, data) in inputs() {
        let bytes: usize = data.iter().map(Vec::len).sum();
        group.throughput(Throughput::Bytes(bytes as u64));
        group.bench_with_input(BenchmarkId::new("trie", name), &data, |b, data| {
            b.iter(|| {
                for d in data {
                    black_box(smaz::compress(black_box(d)));
                }
            })
        });
        group.bench_with_input(BenchmarkId::new("reference", name), &data, |b, data| {
            b.iter(|| {
                for d in data {
                    black_box(smaz_reference::compress(black_box(d)));
                }
            })
        });
    }
    group.finish();
}

fn bench_decompress(c: &mut Criterion) {
    let mut group = c.benchmark_group("decompress");
    for (name, data) in inputs() {
        let compressed: Vec<Vec<u8>> = data.iter().map(|d| smaz::compress(d)).collect();
        let bytes: usize = data.iter().map(Vec::len).sum();
        group.throughput(Throughput::Bytes(bytes as u64));
        group.bench_with_input(BenchmarkId::new("trie", name), &compressed, |b, data| {
            b.iter(|| {
                for d in data {
                    black_box(smaz::decompress(black_box(d)).unwrap());
                }
            })
        });
        group.bench_with_input(
            BenchmarkId::new("reference", name),
            &compressed,
            |b, data| {
                b.iter(|| {
                    for d in data {
                        black_box(smaz_reference::decompress(black_box(d)).unwrap());
                    }
                })
            },
        );
    }
    group.finish();
}

criterion_group!(benches, bench_compress, bench_decompress);
criterion_main!(benches);
