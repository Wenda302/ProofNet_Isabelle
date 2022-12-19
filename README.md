This is a port of [ProofNet](https://github.com/zhangir-azerbayev/ProofNet) to the Isabelle proof assistant.

The task here is to replace the `undefined` symbol in `isabelle_formal/*.thy` with the correct Isabelle formal statement.

For example, the (original) first problem in [Shakarchi.thy](isabelle_formal/Shakarchi.thy) looks like the following:
```
(*
problem_number:1_13a
natural language statement:
Suppose that $f$ is holomorphic in an open set $\Omega$. Prove that if $\text{Re}(f)$ is constant, then $f$ is constant.
lean statement:
theorem exercise_1_13a {f : ℂ → ℂ} (Ω : set ℂ) (a b : Ω) (h : is_open Ω)
  (hf : differentiable_on ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).re = c) :
  f a = f b :=

codex statement:
theorem holomorphic_const_of_real_const:
  fixes f::"complex ⇒ complex"
  assumes "open s" "f holomorphic_on s" "∀x∈s. Re (f x) = c"
  shows "∀x∈s. f x = c"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_13a: undefined oops
```
where in the comment part we have
- a problem identifier (i.e, `problem_number`),
- a natural language statement,
- a Lean statement (if available),
- and an auto-formalised statement from Codex (a large language model).

Here we want to formalise this natural language statement in Isabelle (by replacing the undefined symbol). The Lean statement can often serve as a good hint for our formalisation. If possible, regarding the auto-formalised version from Codex we can leave our one-sentence comment (e.g., good translation, some assumption is missed, totally irrelevant, etc.). In this particular example, the Codex statement is surprisingly decent so that I will simply copy its answer:
```
(*
problem_number:1_13a
natural language statement:
Suppose that $f$ is holomorphic in an open set $\Omega$. Prove that if $\text{Re}(f)$ is constant, then $f$ is constant.
lean statement:
theorem exercise_1_13a {f : ℂ → ℂ} (Ω : set ℂ) (a b : Ω) (h : is_open Ω)
  (hf : differentiable_on ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).re = c) :
  f a = f b :=

codex statement:
theorem holomorphic_const_of_real_const:
  fixes f::"complex ⇒ complex"
  assumes "open s" "f holomorphic_on s" "∀x∈s. Re (f x) = c"
  shows "∀x∈s. f x = c"
Our comment on the codex statement: perfect formalisation.
 *)
theorem exercise_1_13a: 
  fixes f::"complex ⇒ complex"
  assumes "open s" "f holomorphic_on s" "∀x∈s. Re (f x) = c"
  shows "∀x∈s. f x = c" 
  oops
```