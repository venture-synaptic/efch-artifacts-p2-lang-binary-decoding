"""
Backend de LLM para la síntesis guiada (copia de experimento0/llm.py).

Usa el CLI de Claude Code en modo no interactivo (`claude -p`) sin herramientas:
el modelo solo recibe texto y devuelve texto, no puede leer archivos (en
particular, no ve el verificador ni la referencia) ni ejecutar código.
"""

import json
import subprocess
import time

MODEL = "claude-opus-5-5"
EFFORT = "high"
TIMEOUT_S = 600


class LLMError(RuntimeError):
    pass


def complete(system, prompt, model=MODEL, effort=EFFORT):
    """Devuelve {texto, coste_usd, duracion_s, tokens_salida} de una llamada."""
    cmd = ["claude", "-p", "--model", model, "--effort", effort,
           "--tools", "", "--strict-mcp-config", "--no-session-persistence",
           "--output-format", "json", "--system-prompt", system]
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(cmd, input=prompt, capture_output=True, text=True, timeout=TIMEOUT_S)
    except subprocess.TimeoutExpired as e:
        raise LLMError(f"sin respuesta en {TIMEOUT_S} s") from e
    elapsed = time.perf_counter() - t0
    try:
        out = json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        raise LLMError(f"salida no JSON (código {proc.returncode}): {proc.stderr[-500:]}") from e
    if out.get("is_error") or out.get("stop_reason") not in ("end_turn", None):
        raise LLMError(f"llamada fallida: stop_reason={out.get('stop_reason')} {out.get('result', '')[:300]}")
    return {
        "texto": out.get("result", ""),
        "coste_usd": out.get("total_cost_usd"),
        "duracion_s": round(elapsed, 1),
        "tokens_salida": out.get("usage", {}).get("output_tokens"),
    }
