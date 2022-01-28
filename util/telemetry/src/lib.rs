// Copyright (c) 2018-2021 The MobileCoin Foundation

//! OpenTelemetry wrappers and helper utilities.

pub use opentelemetry::{
    trace::{mark_span_as_active, Span, SpanKind, TraceContextExt, Tracer},
    Context, Key,
};

use opentelemetry::{
    global::{tracer_provider, BoxedTracer},
    trace::{SpanBuilder, TraceId, TracerProvider},
};
use std::borrow::Cow;

#[macro_export]
macro_rules! tracer {
    () => {
        $crate::versioned_tracer(
            env!("CARGO_PKG_NAME"),
            Some(env!("CARGO_PKG_VERSION")),
            None,
        )
    };
}

#[macro_export]
macro_rules! telemetry_static_key {
    ($key_name:tt) => {
        $crate::Key::from_static_str(concat!(
            "mobilecoin.com/",
            env!("CARGO_PKG_NAME"),
            "/",
            $key_name
        ))
    };
}

/// A magic value that is used as part of the predictable trace id generated by
/// `block_index_to_trace_id`. (Hex encoding of 'BLKID', chosen arbitrarily)
pub const BLOCK_INDEX_TRACE_ID_MAGIC: u128 = 0x424c4b4944;

// Wrapper around tracer_provider call so users of this lib do not need to
// use GlobalTraceProvider.
pub fn versioned_tracer(
    name: impl Into<Cow<'static, str>>,
    version: Option<&'static str>,
    schema_url: Option<&'static str>,
) -> BoxedTracer {
    tracer_provider().versioned_tracer(name, version, schema_url)
}

/// A utility method to create a predictable trace ID out of a block index.
/// This is used to group traces by block index.
pub fn block_index_to_trace_id(block_index: u64) -> TraceId {
    // Generate a predictable trace id out of the block index.
    // Jaeger displays only the first 7 characters of a trace id and that's where we
    // want our block index to land. 7 hex characters represent 28 bits being
    // displayed, leaving us with 100 bits that need to go to to the right of it.
    // Each character represents 4 bits of the trace id.
    let id: u128 = (block_index as u128) << 100 | BLOCK_INDEX_TRACE_ID_MAGIC;
    TraceId::from_bytes(id.to_be_bytes())
}

/// Create a SpanBuilder and attack the trace ID to a specific block index.
pub fn block_span_builder<T: Tracer>(
    tracer: &T,
    span_name: &'static str,
    block_index: u64,
) -> SpanBuilder {
    tracer
        .span_builder(span_name)
        .with_kind(SpanKind::Server)
        .with_trace_id(block_index_to_trace_id(block_index))
}

/// Start a span tied to a specific block index.
pub fn start_block_span<T: Tracer>(
    tracer: &T,
    span_name: &'static str,
    block_index: u64,
) -> T::Span {
    block_span_builder(tracer, span_name, block_index).start(tracer)
}

cfg_if::cfg_if! {
    if #[cfg(feature = "jaeger")] {
        use displaydoc::Display;
        use opentelemetry::{trace::TraceError, KeyValue, sdk};

        #[derive(Debug, Display)]
        pub enum Error {
            /// Trace error: {0}
            Trace(TraceError),

            /// Get hostname error: {0}
            GetHostname(std::io::Error),

            /// Failed converting hostname to string
            HostnameToString,
        }

        pub fn setup_default_tracer_with_tags(service_name: &str, extra_tags: &[(&'static str, String)]) -> Result<sdk::trace::Tracer, Error> {
            let local_hostname = hostname::get().map_err(Error::GetHostname)?;

            let mut tags = vec![KeyValue::new(
                "hostname",
                local_hostname
                    .to_str()
                    .ok_or(Error::HostnameToString)?
                    .to_owned(),
            )];
            for (key, value) in extra_tags.iter() {
                tags.push(KeyValue::new(*key, value.clone()));
            }

            opentelemetry_jaeger::new_pipeline()
                .with_service_name(service_name)
                .with_trace_config(Config::default().with_resource(Resource::new(tags)))
                .install_simple()
                .map_err(Error::Trace)
        }

        pub fn setup_default_tracer(service_name: &str) -> Result<sdk::trace::Tracer, Error> {
            setup_default_tracer_with_tags(service_name, &[])
        }
    }
}
