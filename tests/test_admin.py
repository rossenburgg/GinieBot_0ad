"""Tests for the token-protected admin dashboard in simple_bot/render_service.py."""

import importlib
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from geniebot_store import GenieBotStore  # noqa: E402

TOKEN = "test-admin-token-123"


@pytest.fixture()
def seeded_db(tmp_path, monkeypatch):
    db_path = str(tmp_path / "admin_test.db")
    monkeypatch.setenv("GENIEBOT_DB", db_path)
    monkeypatch.setenv("ADMIN_TOKEN", TOKEN)
    store = GenieBotStore(db_path)
    store.add_report(1, "reporter1", "badguy", "spamming", room="arena26")
    store.record_offense("badguy", 3)
    store.add_watch("sketchy", added_by="mod")
    store.close()
    return db_path


@pytest.fixture()
def client(seeded_db, monkeypatch):
    monkeypatch.setenv("BOT_ENABLED", "false")  # do not start the XMPP bot
    import simple_bot.render_service as render_service

    importlib.reload(render_service)
    from fastapi.testclient import TestClient

    with TestClient(render_service.app) as test_client:
        yield test_client


def test_stats_requires_token(client):
    resp = client.get("/admin/api/stats")
    assert resp.status_code == 401


def test_stats_with_query_token(client):
    resp = client.get("/admin/api/stats", params={"token": TOKEN})
    assert resp.status_code == 200
    data = resp.json()
    assert data["reports"] == 1
    assert data["offenders"] == 1
    assert data["watchlist"] == 1
    assert data["db"].endswith("admin_test.db")


def test_reports_endpoint(client):
    resp = client.get("/admin/api/reports", params={"token": TOKEN})
    assert resp.status_code == 200
    rows = resp.json()
    assert len(rows) == 1
    assert rows[0]["reported_user"] == "badguy"
    assert rows[0]["reason"] == "spamming"


def test_offenders_endpoint_with_bearer_header(client):
    resp = client.get("/admin/api/offenders", headers={"Authorization": f"Bearer {TOKEN}"})
    assert resp.status_code == 200
    rows = resp.json()
    assert rows[0]["nick"] == "badguy"
    assert rows[0]["offenses"] == 3


def test_watchlist_endpoint(client):
    resp = client.get("/admin/api/watchlist", params={"token": TOKEN})
    assert resp.status_code == 200
    rows = resp.json()
    assert [r["nick"] for r in rows] == ["sketchy"]


def test_wrong_token_rejected(client):
    resp = client.get("/admin/api/stats", params={"token": "nope"})
    assert resp.status_code == 401


def test_dashboard_html_served(client):
    resp = client.get("/admin", params={"token": TOKEN})
    assert resp.status_code == 200
    assert "GinieBot moderation admin" in resp.text


def test_admin_disabled_without_token(tmp_path, monkeypatch):
    monkeypatch.setenv("GENIEBOT_DB", str(tmp_path / "admin_test.db"))
    monkeypatch.delenv("ADMIN_TOKEN", raising=False)
    monkeypatch.setenv("BOT_ENABLED", "false")
    import simple_bot.render_service as render_service

    importlib.reload(render_service)
    from fastapi.testclient import TestClient

    with TestClient(render_service.app) as test_client:
        resp = test_client.get("/admin/api/stats", params={"token": TOKEN})
        assert resp.status_code == 503
