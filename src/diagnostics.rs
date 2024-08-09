use std::{borrow::Cow, fmt::Display};

use crate::Span;

#[must_use]
#[derive(Debug)]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: String,
    pub span: Span,
    pub tags: Vec<Tag>,
}

impl Diagnostic {
    pub fn new(severity: Severity, message: String, span: impl Into<Span>) -> Self {
        Self {
            severity,
            message,
            span: span.into(),
            tags: Vec::new(),
        }
    }

    pub fn tag(mut self, tag: Tag) -> Self {
        self.tags.push(tag);
        self
    }

    pub fn tags(mut self, tags: impl IntoIterator<Item = Tag>) -> Self {
        self.tags.extend(tags);
        self
    }

    pub fn with_primary_tag(self, message: Option<String>) -> Self {
        let tag = Tag::new(
            self.severity,
            message.unwrap_or_else(|| self.message.clone()),
            self.span,
        );

        self.tag(tag)
    }
}

#[derive(Debug)]
pub struct Tag {
    pub severity: Severity,
    pub message: String,
    pub span: Span,
}

impl Tag {
    pub fn new(severity: Severity, message: String, span: impl Into<Span>) -> Self {
        Self {
            severity,
            message,
            span: span.into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    Info,
    Warning,
    Error,
}
