"""Minimal client for TypeSafe's Jev (System One): typed questions about a
state, answered with calibrated probabilities. Key from JEV_API_KEY or
TYPESAFE_API_KEY. Docs: https://docs.typesafe.ai/introduction/quickstart"""
import json, os, urllib.request

URL = "https://api.typesafe.ai/v1/systemone"


def key() -> str:
    k = os.environ.get("JEV_API_KEY") or os.environ.get("TYPESAFE_API_KEY")
    if not k:
        raise RuntimeError("set JEV_API_KEY (it is exported in ~/.zshrc)")
    return k


def system_one(state: str, questions: dict, model: str = "jev-latest") -> dict:
    req = urllib.request.Request(
        URL, data=json.dumps({"model": model, "state": state, "questions": questions}).encode(),
        headers={"Authorization": f"Bearer {key()}", "Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.loads(r.read())["answers"]


def noul(instructions: str) -> dict:
    return {"type": "noul", "instructions": instructions}


def choice(instructions: str, criteria: dict[str, str]) -> dict:
    return {"type": "choice", "instructions": instructions, "criteria": criteria}


def score(instructions: str, criteria: list[str]) -> dict:
    return {"type": "score", "instructions": instructions, "criteria": criteria}
