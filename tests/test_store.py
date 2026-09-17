"""Tests for geniebot_store.py (SQLite persistence)."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from geniebot_store import GenieBotStore


def make_store(tmp_path):
    return GenieBotStore(path=str(tmp_path / "test.db"))


def test_report_round_trip(tmp_path):
    store = make_store(tmp_path)
    store.add_report("abc123", "reporter1", "badguy", reason="spam", room="reports@x")
    reports = store.list_reports()
    assert len(reports) == 1
    row = reports[0]
    assert row["id"] == "abc123"
    assert row["reporter"] == "reporter1"
    assert row["reported_user"] == "badguy"
    assert row["reason"] == "spam"
    assert row["room"] == "reports@x"
    assert row["created_at"]


def test_offender_round_trip(tmp_path):
    store = make_store(tmp_path)
    store.record_offense("troll", 3)
    row = store.get_offender("troll")
    assert row is not None
    assert row["offenses"] == 3
    assert row["last_offense_at"]
    # updating keeps a single row
    store.record_offense("troll", 4)
    assert store.get_offender("troll")["offenses"] == 4
    assert len(store.list_offenders()) == 1
    assert store.get_offender("nobody") is None


def test_watchlist_round_trip(tmp_path):
    store = make_store(tmp_path)
    assert not store.is_watched("suspect")
    store.add_watch("suspect", added_by="mod", force=True)
    assert store.is_watched("suspect")
    watch = store.list_watch()
    assert len(watch) == 1
    assert watch[0]["nick"] == "suspect"
    assert watch[0]["added_by"] == "mod"
    assert watch[0]["force"] == 1
    store.remove_watch("suspect")
    assert not store.is_watched("suspect")
    assert store.list_watch() == []


def test_persistence_across_instances(tmp_path):
    path = str(tmp_path / "persist.db")
    store = GenieBotStore(path=path)
    store.add_report("r1", "a", "b")
    store.record_offense("troll", 2)
    store.add_watch("suspect", added_by="mod")
    store.close()

    reopened = GenieBotStore(path=path)
    assert len(reopened.list_reports()) == 1
    assert reopened.get_offender("troll")["offenses"] == 2
    assert reopened.is_watched("suspect")
    reopened.close()


def test_unwritable_path_falls_back_to_memory(tmp_path):
    # A path under a file (not a directory) cannot be created.
    blocker = tmp_path / "blocker"
    blocker.write_text("x")
    store = GenieBotStore(path=str(blocker / "nested.db"))
    assert store.persistent is False
    store.add_report("r1", "a", "b")
    assert len(store.list_reports()) == 1
    store.close()
