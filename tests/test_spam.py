"""Tests for the smarter spam detection in main.py.

Covers the pre-existing repeated-word check plus the new signals:
rate limiting (>6 messages in 10 s), caps shouting, link floods, and
repeated links across recent messages.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from main import (  # noqa: E402
    SPAM_CAPS_MIN_LENGTH,
    SPAM_LINK_COUNT,
    SPAM_LINK_REPEAT,
    SPAM_RATE_LIMIT_COUNT,
    SPAM_RATE_LIMIT_WINDOW,
    SpamTracker,
    detect_spam,
    is_caps_spam,
)


def test_detect_spam_repeated_word_kept():
    assert detect_spam("hello hello hello hello hello hello world") is True
    assert detect_spam("hello world this is fine") is False


def test_rate_limit_trips_after_six_messages_in_window():
    tracker = SpamTracker()
    reasons = []
    for i in range(SPAM_RATE_LIMIT_COUNT + 1):
        reasons = tracker.record("spammer", f"message number {i}", now=1000.0 + i)
    assert any("rate limit" in r for r in reasons)


def test_rate_limit_resets_after_window_passes():
    tracker = SpamTracker()
    for i in range(SPAM_RATE_LIMIT_COUNT + 1):
        tracker.record("spammer", f"msg {i}", now=1000.0 + i)
    # Far outside the 10 s window the slate is clean again.
    reasons = tracker.record("spammer", "a fresh message", now=1000.0 + SPAM_RATE_LIMIT_WINDOW + 60)
    assert not any("rate limit" in r for r in reasons)


def test_caps_shouting_detected():
    assert is_caps_spam("THIS IS A VERY LOUD MESSAGE") is True
    assert is_caps_spam("This is a normal message, really.") is False
    assert is_caps_spam("short") is False  # below SPAM_CAPS_MIN_LENGTH
    assert is_caps_spam("123456789012") is False  # no letters


def test_caps_min_length_boundary():
    loud = "A" * (SPAM_CAPS_MIN_LENGTH + 5)
    assert is_caps_spam(loud) is True


def test_link_flood_detected():
    tracker = SpamTracker()
    reasons = tracker.record(
        "linker",
        " ".join(f"https://example.com/{i}" for i in range(SPAM_LINK_COUNT + 1)),
        now=2000.0,
    )
    assert any("link spam" in r for r in reasons)


def test_repeated_link_detected():
    tracker = SpamTracker()
    reasons = []
    for i in range(SPAM_LINK_REPEAT):
        reasons = tracker.record("linker", "check https://spam.example/x out", now=3000.0 + i)
    assert any("repeated link" in r for r in reasons)


def test_single_link_is_clean():
    tracker = SpamTracker()
    reasons = tracker.record("normal", "see https://example.com/cool for details", now=4000.0)
    assert reasons == []


def test_tracker_is_per_sender():
    tracker = SpamTracker()
    for i in range(SPAM_RATE_LIMIT_COUNT + 1):
        tracker.record("spammer", f"msg {i}", now=5000.0 + i)
    assert tracker.record("innocent", "just one message", now=5000.0) == []
