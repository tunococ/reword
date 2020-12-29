use std::fs;

use criterion::{black_box, criterion_group, Criterion};

use reword::io::*;

fn consume_iterator<I: Iterator>(i: I) -> usize {
    let mut count: usize = 0;
    for x in i {
        black_box(x);
        count += 1;
    }
    count
}

fn bench_decode_utf8_stream_from_file(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode_utf8_from_file");

    const PATH: &str = "test_data/utf8_all_chars.txt";

    group.bench_function("baseline (built-in)", |b| b.iter(|| {
        let s = fs::read_to_string(PATH).unwrap();
        let stream = s.chars();
        black_box(consume_iterator(stream));
    }));
    group.bench_function("batch size: MAX", |b| b.iter(|| {
        let stream = read_utf8_stream(PATH, usize::MAX).unwrap();
        black_box(consume_iterator(stream));
    }));
    group.bench_function("batch size: 64KiB", |b| b.iter(|| {
        let stream = read_utf8_stream(PATH, 64 << 10).unwrap();
        black_box(consume_iterator(stream));
    }));
    group.bench_function("batch size: 8KiB", |b| b.iter(|| {
        let stream = read_utf8_stream(PATH, 8 << 10).unwrap();
        black_box(consume_iterator(stream));
    }));

    group.finish();
}

criterion_group!(bench, bench_decode_utf8_stream_from_file);
