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
- a problem identifier (e.g. `1_13a`),
- a natural language statement,
- a Lean statement (if available),
- and an auto-formalised statement from Codex (a large language model).

Here we want to formalise this natural language statement in Isabelle (by replacing the undefined symbol). The Lean statement can often serve as a good hint for our formalisation. If possible, regarding the auto-formalised version from Codex we can leave our one-sentence comment (e.g., good translation, some assumption is missed, totally irrelevant, etc.). In this particular example, the Codex statement is mostly correct but is slightly wrong for the conclusion part. I commented on this issue and then posted my formalisation:
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
Our comment on the codex statement: f is constant but not necessary equal to c.
 *)
theorem exercise_1_13a: 
  fixes f::"complex ⇒ complex"
  assumes "open s" "f holomorphic_on s" "∀x∈s. Re (f x) = c"
  shows "∃ c. ∀x∈s. f x = c"
  oops
```

PS: we may sometimes need to change the 'imports' part of the target theory file when the background theories are missing.

### Status
- [ ] [Artin.thy](isabelle_formal/Artin.thy)  
- [ ] [Axler.thy](isabelle_formal/Axler.thy)  
- [x] [Cambridge-Tripos.thy](isabelle_formal/Cambridge-Tripos.thy)  
- [ ] [Dummit-Foote.thy](isabelle_formal/Dummit-Foote.thy)  
- [x] [Herstein.thy](isabelle_formal/Herstein.thy): 
- [x] [Ireland-Rosen.thy](isabelle_formal/Ireland-Rosen.thy)  
- [x] [Munkres.thy](isabelle_formal/Munkres.thy)  
- [x] [Pugh.thy](isabelle_formal/Pugh.thy)  
- [x] [Putnam.thy](isabelle_formal/Putnam.thy)
- [ ] [Rudin.thy](isabelle_formal/Rudin.thy): in progress by Angeliki
- [x] [Shakarchi.thy](isabelle_formal/Shakarchi.thy)

