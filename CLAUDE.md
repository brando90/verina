# Claude Code: read `~/agents-config/INDEX_RULES.md` for all agent documentation and routing.
# If `~/agents-config/` is not present, clone it: `git clone https://github.com/brando90/agents-config.git ~/agents-config`

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Verina (Verifiable Code Generation Arena) is a benchmark for evaluating code, specification, and proof generation using Lean 4. It supports modular evaluation of generation tasks and their compositions.

## Common Commands

```bash
# Setup
uv sync
source .venv/bin/activate
lake exe cache get && lake update

# For Lean v4.24 (enables grind tactic)
./setup_lean_v424.sh

# Start Prefect server (required for benchmarks)
docker compose up -d  # PostgreSQL for Prefect
uv run prefect server start

# Run benchmarks
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/benchmark.py -c configs/<config>.toml

# Generation only / Evaluation only
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/benchmark.py -c configs/<config>.toml --no-eval
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/benchmark.py -c configs/<config>.toml --no-gen -ew <workers>

# Quality assurance
PREFECT_API_URL=http://127.0.0.1:4200/api uv run scripts/quality_assurance.py -c configs/qa.toml

# Code formatting (also runs via pre-commit hooks)
ruff check --select I --fix  # Sort imports
ruff format
```

## Architecture

### Core Components (`src/verina/`)

- **benchmark/**: Orchestration framework using Prefect
  - `solution.py`: Abstract `Solution` class - subclass this for custom solutions
  - `benchmark.py`: Main Prefect flow orchestration
  - `evaluation_tasks.py`: Task execution and evaluation logic
  - `metrics.py`: Evaluation metrics (unit tests, formal proving, compilation)

- **baseline/**: Reference implementations
  - `baseline.py`: `BaselineSolution` using DSPy for generation
  - `generate.py`: DSPy-based code/spec/proof generation
  - `proof_refinement.py`: Iterative proof refinement strategy

- **dataset/**: Data loading and Lean templating
  - `schema.py`: Pydantic models (BenchmarkData, Signature, etc.)
  - `template.py`: Lean code template rendering with variable substitution

- **utils/lm.py**: LLM provider abstraction (OpenAI, Anthropic, Vertex AI, Together AI, local/vLLM)

### Task Types

- **Basic**: `code_gen`, `spec_gen`, `proof_gen`
- **Combined**: `code_spec_gen`, `code_proof_gen`, `spec_proof_gen`, `code_spec_proof_gen`

Combined tasks use preferences to decide between reference or generated artifacts.

### Dataset Structure (`datasets/verina/`)

Each task folder contains:
- `task.json`: Metadata and file paths
- `description.txt`: Natural language task description
- `task.lean`: Ground truth Lean 4 code/spec/proof
- `test.json`, `reject_inputs.json`: Test cases

### Configuration

TOML files in `configs/` control:
- `output_dir`, `max_workers`, `rounds`
- Task selection flags (which gen tasks to run)
- `[gen_lm_config]`: LLM provider and model
- `[baseline_config]`: Method selection (`baseline`, `proof_refinement`, `custom_prompt_baseline`, etc.)

## Key Patterns

- **DSPy Signatures**: Prompts are defined as DSPy Signature classes, not raw templates
- **Prefect Caching**: Results are cached; use new `output_dir` or set `refresh_cache = true` in `prefect.toml` to avoid stale results
- **Async/Await**: Heavy use of Python async for concurrent Prefect task execution
- **Pydantic V2**: Structured validation throughout

## Creating Custom Solutions

Inherit from `Solution` (or `SimpleSolution` for automatic combined task derivation) in `benchmark/solution.py`. See `BaselineSolution` in `baseline/baseline.py` as reference.
