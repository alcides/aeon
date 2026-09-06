"""Runtime helpers for ``libraries/Email.ae`` fluent drafts."""

from __future__ import annotations


def new_email():
    return {"phase": 1, "sender": None, "to": [], "subject": "", "body": None}


def set_from(sender, draft):
    return {**draft, "phase": 2, "sender": sender}


def add_to(receiver, draft):
    receivers = list(draft["to"])
    receivers.append(receiver)
    return {**draft, "phase": 3, "to": receivers}


def set_subject(subject, draft):
    return {**draft, "subject": subject}


def set_body(body, draft):
    return {**draft, "phase": 4, "body": body}


def build(draft):
    receivers = ", ".join(draft["to"])
    subject = draft["subject"] or "(no subject)"
    return f"From: {draft['sender']}\nTo: {receivers}\nSubject: {subject}\n\n{draft['body']}"
