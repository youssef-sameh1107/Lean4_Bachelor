[Read the full bachelor’s thesis (PDF)](Evaluating Large Language Models for Machine-Checked Proofs in Lean 4_ A Case Study in Formal Languages.pdf)

# Evaluating Large Language Models for Machine-Checked Proofs in Lean 4

Bachelor’s thesis project by Yousef Sameh Mourid Mohamad Mohamad Elbaz at the German University in Cairo, supervised by Dr. Ulf Krumnack.

## Formalization

The case study is closure of regular languages under concatenation. The manually written reference proof in [`proof.lean`](proof.lean) constructs an ε-NFA for two DFAs and proves that its accepted language is the concatenation of the two input languages. The theorem `εNFA.concat_accepts` states the central acceptance equality, and the file ends with a `#print axioms` command for inspecting its dependencies.

## Evaluation

The main experiment compared three hosted model configurations at three levels of guidance, with five runs per configuration and level. The prompts ranged from an unguided request to a scaffold that supplied the central automaton construction.

Each submission was assessed in order:

1. **Statement fidelity** checks whether the submission formalizes the intended target using the relevant Mathlib definitions.
2. **Proof completeness** checks whether the submission provides a complete Lean proof of that target.

| Outcome | Runs |
| --- | ---: |
| Substituted a different formal target | 12 |
| Preserved the target but did not complete the proof | 29 |
| Completed the intended proof | 4 |
| **Total** | **45** |

All 12 target substitutions occurred under unguided prompting. Of the 29 statement-faithful failures, 28 contained no explicit proof placeholder. Three supplementary runs from a fourth configuration were reported separately in the thesis. The results describe this one theorem and experimental setup.

## Check the reference proof

The repository pins Lean and Mathlib to **v4.30.0**. With Elan installed, run these commands from the repository root:

```sh
lake exe cache get
lake env lean proof.lean
```

Use the file-specific command to check the reference proof and see its axiom report. The model submissions include incomplete and rejected attempts.

## Repository contents

| Path | Contents |
| --- | --- |
| [`proof.lean`](proof.lean) | Manually written reference proof |
| [`lemma_only.lean`](lemma_only.lean) | Construction and lemma scaffold with intentional `sorry` placeholders |
| [`Bachelor_thesis_Real/`](Bachelor_thesis_Real/) and [`restored/`](restored/) | Experimental Lean files, including model submissions organized by configuration and guidance level |
| [`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml), [`lake-manifest.json`](lake-manifest.json) | Toolchain and dependency configuration |
