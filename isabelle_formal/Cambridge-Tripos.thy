theory "Cambridge-Tripos"
 imports Main
begin

(*
problem_number:2022_IA_1-II-9D-a
natural language statement:
Let $a_{n}$ be a sequence of real numbers. Show that if $a_{n}$ converges, the sequence $\frac{1}{n} \sum_{k=1}^{n} a_{k}$ also converges and $\lim _{n \rightarrow \infty} \frac{1}{n} \sum_{k=1}^{n} a_{k}=\lim _{n \rightarrow \infty} a_{n}$.
lean statement:

codex statement:
theorem lim_sum_div_n_eq_lim:
  fixes f::"nat ⇒ 'a::real_normed_vector"
  assumes "convergent f"
  shows "convergent (λn. (∑i<n. f i) / n) ∧ lim (λn. (∑i<n. f i) / n) = lim f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IA_1-II-9D-a": undefined oops


(*
problem_number:2022_IA_1-II-10D-c
natural language statement:
Let a function $g:(0, \infty) \rightarrow \mathbb{R}$ be continuous and bounded. Show that for every $T>0$ there exists a sequence $x_{n}$ such that $x_{n} \rightarrow \infty$ and $\lim _{n \rightarrow \infty}\left(g\left(x_{n}+T\right)-g\left(x_{n}\right)\right)=0 .$
lean statement:

codex statement:
theorem exists_seq_tendsto_infty_of_continuous_bounded:
  fixes g::"real ⇒ real"
  assumes "continuous_on {0<..} g" "bounded (range g)"
  shows "∀T>0. ∃x. x⟶∞ ∧ (∀n. g (x n + T) - g (x n) ⟶ 0)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IA_1-II-10D-c": undefined oops


(*
problem_number:2022_IA_4-I-1E-a
natural language statement:
By considering numbers of the form $3 p_{1} \ldots p_{k}-1$, show that there are infinitely many primes of the form $3 n+2$ with $n \in \mathbb{N}$.
lean statement:

codex statement:
theorem exists_infinite_primes_of_form_3n_plus_2:
  fixes n::nat
  assumes "∀p. prime p ⟶ p ∣ n ⟶ p = 2 ∨ p = 3"
  shows "∃p. prime p ∧ p ∣ n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IA_4-I-1E-a": undefined oops


(*
problem_number:2022_IA_4-I-2D-a
natural language statement:
Prove that $\sqrt[3]{2}+\sqrt[3]{3}$ is irrational.
lean statement:

codex statement:
theorem irrational_of_sum_of_irrational_roots:
  assumes "∀x y. x^3 = 2 ∧ y^3 = 3 ⟶ x = y"
  shows "∀x y. x^3 = 2 ∧ y^3 = 3 ⟶ x + y ≠ 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IA_4-I-2D-a": undefined oops


(*
problem_number:2022_IB_3-II-13G-a-i
natural language statement:
Let $U \subset \mathbb{C}$ be a (non-empty) connected open set and let $f_n$ be a sequence of holomorphic functions defined on $U$. Suppose that $f_n$ converges uniformly to a function $f$ on every compact subset of $U$. Show that $f$ is holomorphic in $U$.
lean statement:

codex statement:
theorem holomorphic_of_uniform_convergent_holomorphic:
  fixes f::"complex ⇒ complex" and f::"nat ⇒ complex ⇒ complex"
  assumes "open U" "connected U" "∀n. holomorphic_on U (f n)" "∀K. compact K ⊆ U ⟶ uniform_limit (f n) f (uniformity_on K)"
  shows "holomorphic_on U f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IB_3-II-13G-a-i": undefined oops


(*
problem_number:2022_IB_3-II-11G-b
natural language statement:
Let $f: \mathbb{R}^{2} \rightarrow \mathbb{R}^{2}$ be the map given by $f(x, y)=\left(\frac{\cos x+\cos y-1}{2}, \cos x-\cos y\right)$. Prove that $f$ has a fixed point.
lean statement:

codex statement:
theorem exists_fixed_point_of_f:
  fixes f::"real ⇒ real ⇒ real"
  assumes "f = (λx y. (cos x + cos y - 1)/2, cos x - cos y)"
  shows "∃x. f x = x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IB_3-II-11G-b": undefined oops


(*
problem_number:2022_IB_1-I-3G-i
natural language statement:
Show that $f(z)=\frac{z}{\sin z}$ has a removable singularity at $z=0$.
lean statement:

codex statement:
theorem removable_singularity_sin_z:
  fixes f::"complex ⇒ complex"
  assumes "f holomorphic_on {z. z ≠ 0}" "f 0 = 0"
  shows "f holomorphic_on UNIV"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IB_1-I-3G-i": undefined oops


(*
problem_number:2022_IB_3-I-1E-ii
natural language statement:
Let $R$ be a subring of a ring $S$, and let $J$ be an ideal in $S$. Show that $R+J$ is a subring of $S$ and that $\frac{R}{R \cap J} \cong \frac{R+J}{J}$.
lean statement:

codex statement:
theorem is_ring_of_subring_plus_ideal:
  fixes R S::"'a::comm_ring_1 ring" and J::"'a ring"
  assumes "subring R S" "ideal J S"
  shows "subring (R + J) S"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IB_3-I-1E-ii": undefined oops


(*
problem_number:2022_IIB_1-II-8F-a-i
natural language statement:
Let $V$ be a finite dimensional complex inner product space, and let $\alpha$ be an endomorphism of $V$. Define its adjoint $\alpha^*$. Assume that $\alpha$ is normal, i.e. $\alpha$ commutes with its adjoint: $\alpha \alpha^*=\alpha^* \alpha$. Show that $\alpha$ and $\alpha^*$ have a common eigenvector $\mathbf{v}$.
lean statement:

codex statement:
theorem exists_common_eigenvector_of_normal_endomorphism:
  fixes V::"complex vector" and α::"complex ⇒ complex"
  assumes "finite_dimensional V" "inner_product_space V" "linear α" "α o α = α o α"
  shows "∃v. v ≠ 0 ∧ (α v = α v) ∧ (α v = α v)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IIB_1-II-8F-a-i": undefined oops


(*
problem_number:2021_IIB_3-II-11F-ii
natural language statement:
Let $X$ be an open subset of Euclidean space $\mathbb{R}^n$. Show that $X$ is connected if and only if $X$ is path-connected.
lean statement:

codex statement:
theorem connected_of_path_connected:
  fixes X::"'a::euclidean_space set"
  assumes "open X" "path_connected X"
  shows "connected X"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2021_IIB_3-II-11F-ii": undefined oops


(*
problem_number:2021_IIB_2-I-1G
natural language statement:
Let $M$ be a module over a Principal Ideal Domain $R$ and let $N$ be a submodule of $M$. Show that $M$ is finitely generated if and only if $N$ and $M / N$ are finitely generated.
lean statement:

codex statement:
theorem finitely_generated_of_finitely_generated_quotient_and_submodule:
  fixes R::"'a::comm_ring_1" and M::"'a module" and N::"'a module"
  assumes "PID R" "submodule N M"
  shows "finitely_generated R M ⟷ finitely_generated R N ∧ finitely_generated R (quotient_module.quotient N)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2021_IIB_2-I-1G": undefined oops


(*
problem_number:2021_IIB_3-I-1G-i
natural language statement:
Let $G$ be a finite group, and let $H$ be a proper subgroup of $G$ of index $n$. Show that there is a normal subgroup $K$ of $G$ such that $|G / K|$ divides $n$ ! and $|G / K| \geqslant n$
lean statement:

codex statement:
theorem exists_normal_subgroup_of_index_divides_factorial:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "subgroup H G" "finite_index G H"
  shows "∃K. normal_subgroup K G ∧ card (G / K) dvd card (H / (𝟭 H)) ∧ card (G / K) ≥ card (H / (𝟭 H))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2021_IIB_3-I-1G-i": undefined oops


(*
problem_number:2021_IIB_1-II-9G-v
natural language statement:
Let $R$ be the ring of continuous functions $\mathbb{R}\to\mathbb{R}$. Show that $R$ is not Noetherian.
lean statement:

codex statement:
theorem not_noetherian_of_continuous_functions:
  fixes R::"('a::euclidean_space ⇒ 'b::euclidean_space) ring"
  assumes "continuous_on UNIV f" "continuous_on UNIV g"
  shows "∃I. ideal I R ∧ ∀J. ideal J R ⟶ J ⊆ I ⟶ J = I"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2021_IIB_1-II-9G-v": undefined oops


(*
problem_number:2018_IA_1-I-3E-b
natural language statement:
Let $f: \mathbb{R} \rightarrow(0, \infty)$ be a decreasing function. Let $x_{1}=1$ and $x_{n+1}=x_{n}+f\left(x_{n}\right)$. Prove that $x_{n} \rightarrow \infty$ as $n \rightarrow \infty$.
lean statement:

codex statement:
theorem tendsto_at_top_of_decreasing_seq:
  fixes f::"real ⇒ real"
  assumes "decseq f" "∀x. f x > 0"
  shows "(∑i<n. f i) ⟶ ∞"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2018_IA_1-I-3E-b": undefined oops




end