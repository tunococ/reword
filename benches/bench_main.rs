use criterion::criterion_main;

mod utf8_converters;

criterion_main!(
    utf8_converters::bench
);
