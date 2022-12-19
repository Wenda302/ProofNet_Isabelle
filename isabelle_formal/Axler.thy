theory Axler
 imports Complex_Main
begin

(*
problem_number:1_2
natural language statement:
Show that $\frac{-1 + \sqrt{3}i}{2}$ is a cube root of 1 (meaning that its cube equals 1).
lean statement:
theorem exercise_1_2 :
  (⟨-1/2, real.sqrt 3 / 2⟩ : ℂ) ^ 3 = -1 :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: entire_function is not relavent here.
 *)
theorem exercise_1_2: "(-1/2 + sqrt 3 * 𝗂 /2)^3 = -1" oops


(*
problem_number:1_3
natural language statement:
Prove that $-(-v) = v$ for every $v \in V$.
lean statement:
theorem exercise_1_3 {F V : Type*} [add_comm_group V] [field F]
  [module F V] {v : V} : -(-v) = v :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real and z::complex
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_3: undefined oops


(*
problem_number:1_4
natural language statement:
Prove that if $a \in \mathbf{F}$, $v \in V$, and $av = 0$, then $a = 0$ or $v = 0$.
lean statement:
theorem exercise_1_4 {F V : Type*} [add_comm_group V] [field F]
  [module F V] (v : V) (a : F): a • v = 0 ↔ a = 0 ∨ v = 0 :=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real and z::complex
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_4: undefined oops


(*
problem_number:1_6
natural language statement:
Give an example of a nonempty subset $U$ of $\mathbf{R}^2$ such that $U$ is closed under addition and under taking additive inverses (meaning $-u \in U$ whenever $u \in U$), but $U$ is not a subspace of $\mathbf{R}^2$.
lean statement:
theorem exercise_1_6 : ∃ U : set (ℝ × ℝ),
  (U ≠ ∅) ∧
  (∀ (u v : ℝ × ℝ), u ∈ U ∧ v ∈ U → u + v ∈ U) ∧
  (∀ (u : ℝ × ℝ), u ∈ U → -u ∈ U) ∧
  (∀ U' : submodule ℝ (ℝ × ℝ), U ≠ ↑U') :=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_6: undefined oops


(*
problem_number:1_7
natural language statement:
Give an example of a nonempty subset $U$ of $\mathbf{R}^2$ such that $U$ is closed under scalar multiplication, but $U$ is not a subspace of $\mathbf{R}^2$.
lean statement:
theorem exercise_1_7 : ∃ U : set (ℝ × ℝ),
  (U ≠ ∅) ∧
  (∀ (c : ℝ) (u : ℝ × ℝ), u ∈ U → c • u ∈ U) ∧
  (∀ U' : submodule ℝ (ℝ × ℝ), U ≠ ↑U') :=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_7: undefined oops


(*
problem_number:1_8
natural language statement:
Prove that the intersection of any collection of subspaces of $V$ is a subspace of $V$.
lean statement:
theorem exercise_1_8 {F V : Type*} [add_comm_group V] [field F]
  [module F V] {ι : Type*} (u : ι → submodule F V) :
  ∃ U : submodule F V, (⋂ (i : ι), (u i).carrier) = ↑U :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_8: undefined oops


(*
problem_number:1_9
natural language statement:
Prove that the union of two subspaces of $V$ is a subspace of $V$ if and only if one of the subspaces is contained in the other.
lean statement:
theorem exercise_1_9 {F V : Type*} [add_comm_group V] [field F]
  [module F V] (U W : submodule F V):
  ∃ U' : submodule F V, U'.carrier = ↑U ∩ ↑W ↔ U ≤ W ∨ W ≤ U :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real and z::complex
  assumes "α > 0"
  shows "entire_function (λn. z^n / (fact n)^α)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_9: undefined oops


(*
problem_number:2_1
natural language statement:
Prove that if $\left(v_{1}, \ldots, v_{n}\right)$ spans $V$, then so does the list $\left(v_{1}-v_{2}, v_{2}-v_{3}, \ldots, v_{n-1}-v_{n}, v_{n}\right)$ obtained by subtracting from each vector (except the last one) the following vector.
lean statement:

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_1: undefined oops


(*
problem_number:2_2
natural language statement:
Prove that if $\left(v_{1}, \ldots, v_{n}\right)$ is linearly independent in $V$, then so is the list $\left(v_{1}-v_{2}, v_{2}-v_{3}, \ldots, v_{n-1}-v_{n}, v_{n}\right)$ obtained by subtracting from each vector (except the last one) the following vector.
lean statement:

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real and z::complex
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_2: undefined oops


(*
problem_number:2_6
natural language statement:
Prove that the real vector space consisting of all continuous realvalued functions on the interval $[0,1]$ is infinite dimensional.
lean statement:

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_6: undefined oops


(*
problem_number:3_1
natural language statement:
Show that every linear map from a one-dimensional vector space to itself is multiplication by some scalar. More precisely, prove that if $\operatorname{dim} V=1$ and $T \in \mathcal{L}(V, V)$, then there exists $a \in \mathbf{F}$ such that $T v=a v$ for all $v \in V$.
lean statement:
theorem exercise_3_1 {F V : Type*}  
  [add_comm_group V] [field F] [module F V] [finite_dimensional F V]
  (T : V →ₗ[F] V) (hT : finrank F V = 1) :
  ∃ c : F, ∀ v : V, T v = c • v:=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_1: undefined oops


(*
problem_number:3_8
natural language statement:
Suppose that $V$ is finite dimensional and that $T \in \mathcal{L}(V, W)$. Prove that there exists a subspace $U$ of $V$ such that $U \cap \operatorname{null} T=\{0\}$ and range $T=\{T u: u \in U\}$.
lean statement:
theorem exercise_3_8 {F V W : Type*}  [add_comm_group V]
  [add_comm_group W] [field F] [module F V] [module F W]
  (L : V →ₗ[F] W) :
  ∃ U : submodule F V, U ⊓ L.ker = ⊥ ∧
  linear_map.range L = range (dom_restrict L U):=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_8: undefined oops


(*
problem_number:3_9
natural language statement:
Prove that if $T$ is a linear map from $\mathbf{F}^{4}$ to $\mathbf{F}^{2}$ such that $\operatorname{null} T=\left\{\left(x_{1}, x_{2}, x_{3}, x_{4}\right) \in \mathbf{F}^{4}: x_{1}=5 x_{2}\right.$ and $\left.x_{3}=7 x_{4}\right\}$, then $T$ is surjective.
lean statement:

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_9: undefined oops


(*
problem_number:3_10
natural language statement:
Prove that there does not exist a linear map from $\mathbf{F}^{5}$ to $\mathbf{F}^{2}$ whose null space equals $\left\{\left(x_{1}, x_{2}, x_{3}, x_{4}, x_{5}\right) \in \mathbf{F}^{5}: x_{1}=3 x_{2} \text { and } x_{3}=x_{4}=x_{5}\right\} .$
lean statement:

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_10: undefined oops


(*
problem_number:3_11
natural language statement:
Prove that if there exists a linear map on $V$ whose null space and range are both finite dimensional, then $V$ is finite dimensional.
lean statement:

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_11: undefined oops


(*
problem_number:4_4
natural language statement:
Suppose $p \in \mathcal{P}(\mathbf{C})$ has degree $m$. Prove that $p$ has $m$ distinct roots if and only if $p$ and its derivative $p^{\prime}$ have no roots in common.
lean statement:
theorem exercise_4_4 (p : polynomial ℂ) :
  p.degree = @card (root_set p ℂ) (polynomial.root_set_fintype p ℂ) ↔
  disjoint
  (@card (root_set p.derivative ℂ) (polynomial.root_set_fintype p.derivative ℂ))
  (@card (root_set p ℂ) (polynomial.root_set_fintype p ℂ)) :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real and z::complex
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4: undefined oops


(*
problem_number:5_1
natural language statement:
Suppose $T \in \mathcal{L}(V)$. Prove that if $U_{1}, \ldots, U_{m}$ are subspaces of $V$ invariant under $T$, then $U_{1}+\cdots+U_{m}$ is invariant under $T$.
lean statement:
theorem exercise_5_1 {F V : Type*} [add_comm_group V] [field F]
  [module F V] {L : V →ₗ[F] V} {n : ℕ} (U : fin n → submodule F V)
  (hU : ∀ i : fin n, map L (U i) = U i) :
  map L (∑ i : fin n, U i : submodule F V) =
  (∑ i : fin n, U i : submodule F V) :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_1: undefined oops


(*
problem_number:5_4
natural language statement:
Suppose that $S, T \in \mathcal{L}(V)$ are such that $S T=T S$. Prove that $\operatorname{null} (T-\lambda I)$ is invariant under $S$ for every $\lambda \in \mathbf{F}$.
lean statement:
theorem exercise_5_4 {F V : Type*} [add_comm_group V] [field F]
  [module F V] (S T : V →ₗ[F] V) (hST : S ∘ T = T ∘ S) (c : F):
  map S (T - c • id).ker = (T - c • id).ker :=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_4: undefined oops


(*
problem_number:5_11
natural language statement:
Suppose $S, T \in \mathcal{L}(V)$. Prove that $S T$ and $T S$ have the same eigenvalues.
lean statement:
theorem exercise_5_11 {F V : Type*} [add_comm_group V] [field F]
  [module F V] (S T : End F V) :
  (S * T).eigenvalues = (T * S).eigenvalues  :=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_11: undefined oops


(*
problem_number:5_12
natural language statement:
Suppose $T \in \mathcal{L}(V)$ is such that every vector in $V$ is an eigenvector of $T$. Prove that $T$ is a scalar multiple of the identity operator.
lean statement:
theorem exercise_5_12 {F V : Type*} [add_comm_group V] [field F]
  [module F V] {S : End F V}
  (hS : ∀ v : V, ∃ c : F, v ∈ eigenspace S c) :
  ∃ c : F, S = c • id :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_12: undefined oops


(*
problem_number:5_13
natural language statement:
Suppose $T \in \mathcal{L}(V)$ is such that every subspace of $V$ with dimension $\operatorname{dim} V-1$ is invariant under $T$. Prove that $T$ is a scalar multiple of the identity operator.
lean statement:
theorem exercise_5_13 {F V : Type*} [add_comm_group V] [field F]
  [module F V] [finite_dimensional F V] {T : End F V}
  (hS : ∀ U : submodule F V, finrank F U = finrank F V - 1 →
  map T U = U) : ∃ c : F, T = c • id :=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_13: undefined oops


(*
problem_number:5_20
natural language statement:
Suppose that $T \in \mathcal{L}(V)$ has $\operatorname{dim} V$ distinct eigenvalues and that $S \in \mathcal{L}(V)$ has the same eigenvectors as $T$ (not necessarily with the same eigenvalues). Prove that $S T=T S$.
lean statement:
theorem exercise_5_20 {F V : Type*} [add_comm_group V] [field F]
  [module F V] [finite_dimensional F V] {S T : End F V}
  (h1 : @card T.eigenvalues (eigenvalues.fintype T) = finrank F V)
  (h2 : ∀ v : V, ∃ c : F, v ∈ eigenspace S c ↔ ∃ c : F, v ∈ eigenspace T c) :
  S * T = T * S :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_20: undefined oops


(*
problem_number:5_24
natural language statement:
Suppose $V$ is a real vector space and $T \in \mathcal{L}(V)$ has no eigenvalues. Prove that every subspace of $V$ invariant under $T$ has even dimension.
lean statement:
theorem exercise_5_24 {V : Type*} [add_comm_group V]
  [module ℝ V] [finite_dimensional ℝ V] {T : End ℝ V}
  (hT : ∀ c : ℝ, eigenspace T c = ⊥) {U : submodule ℝ V}
  (hU : map T U = U) : even (finrank U) :=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_24: undefined oops


(*
problem_number:6_2
natural language statement:
Suppose $u, v \in V$. Prove that $\langle u, v\rangle=0$ if and only if $\|u\| \leq\|u+a v\|$ for all $a \in \mathbf{F}$.
lean statement:
theorem exercise_6_2 {V : Type*} [add_comm_group V] [module ℂ V]
  [inner_product_space ℂ V] (u v : V) :
  ⟪u, v⟫_ℂ = 0 ↔ ∀ (a : ℂ), ∥u∥ ≤ ∥u + a • v∥ :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_2: undefined oops


(*
problem_number:6_3
natural language statement:
Prove that $\left(\sum_{j=1}^{n} a_{j} b_{j}\right)^{2} \leq\left(\sum_{j=1}^{n} j a_{j}{ }^{2}\right)\left(\sum_{j=1}^{n} \frac{b_{j}{ }^{2}}{j}\right)$ for all real numbers $a_{1}, \ldots, a_{n}$ and $b_{1}, \ldots, b_{n}$.
lean statement:
theorem exercise_6_3 {n : ℕ} (a b : fin n → ℝ) :
  (∑ i, a i * b i) ^ 2 ≤ (∑ i : fin n, i * a i ^ 2) * (∑ i, b i ^ 2 / i) :=

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_3: undefined oops


(*
problem_number:6_7
natural language statement:
Prove that if $V$ is a complex inner-product space, then $\langle u, v\rangle=\frac{\|u+v\|^{2}-\|u-v\|^{2}+\|u+i v\|^{2} i-\|u-i v\|^{2} i}{4}$ for all $u, v \in V$.
lean statement:
theorem exercise_6_7 {V : Type*} [inner_product_space ℂ V] (u v : V) :
  ⟪u, v⟫_ℂ = (∥u + v∥^2 - ∥u - v∥^2 + I*∥u + I•v∥^2 - I*∥u-I•v∥^2) / 4 :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real and z::complex
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_7: undefined oops


(*
problem_number:6_13
natural language statement:
Suppose $\left(e_{1}, \ldots, e_{m}\right)$ is an or thonormal list of vectors in $V$. Let $v \in V$. Prove that $\|v\|^{2}=\left|\left\langle v, e_{1}\right\rangle\right|^{2}+\cdots+\left|\left\langle v, e_{m}\right\rangle\right|^{2}$ if and only if $v \in \operatorname{span}\left(e_{1}, \ldots, e_{m}\right)$.
lean statement:
theorem exercise_6_13 {V : Type*} [inner_product_space ℂ V] {n : ℕ}
  {e : fin n → V} (he : orthonormal ℂ e) (v : V) :
  ∥v∥^2 = ∑ i : fin n, ∥⟪v, e i⟫_ℂ∥^2 ↔ v ∈ span ℂ (e '' univ) :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_13: undefined oops


(*
problem_number:6_16
natural language statement:
Suppose $U$ is a subspace of $V$. Prove that $U^{\perp}=\{0\}$ if and only if $U=V$
lean statement:
theorem exercise_6_16 {K V : Type*} [is_R_or_C K] [inner_product_space K V]
  {U : submodule K V} : 
  U.orthogonal = ⊥  ↔ U = ⊤ :=

codex statement:
theorem entire_function_of_order_one_over_alpha:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_16: undefined oops


(*
problem_number:6_17
natural language statement:
Prove that if $P \in \mathcal{L}(V)$ is such that $P^{2}=P$ and every vector in $\operatorname{null} P$ is orthogonal to every vector in $\operatorname{range} P$, then $P$ is an orthogonal projection.
lean statement:

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_17: undefined oops


(*
problem_number:6_18
natural language statement:
Prove that if $P \in \mathcal{L}(V)$ is such that $P^{2}=P$ and $\|P v\| \leq\|v\|$ for every $v \in V$, then $P$ is an orthogonal projection.
lean statement:

codex statement:
theorem entire_of_sum_frac_power_factorial:
  fixes α::real
  assumes "α > 0"
  shows "entire_function (λz. (∑n. z^n / (fact n)^α))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_18: undefined oops


(*
problem_number:6_19
natural language statement:
Suppose $T \in \mathcal{L}(V)$ and $U$ is a subspace of $V$. Prove that $U$ is invariant under $T$ if and only if $P_{U} T P_{U}=T P_{U}$.
lean statement:

codex statement:
theorem invariant_of_projection_eq_projection_comp:
  fixes T::"'a::euclidean_space ⇒ 'a" and U::"'a set"
  assumes "subspace U"
  shows "invariant_under T U ⟷ (T ∘ (projection U) = projection U ∘ T)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_19: undefined oops


(*
problem_number:6_20
natural language statement:
Suppose $T \in \mathcal{L}(V)$ and $U$ is a subspace of $V$. Prove that $U$ and $U^{\perp}$ are both invariant under $T$ if and only if $P_{U} T=T P_{U}$.
lean statement:

codex statement:
theorem orthogonal_projection_eq_projection_orthogonal:
  fixes T::"'a::euclidean_space ⇒ 'a" and U::"'a set"
  assumes "subspace U"
  shows "(T ` U) ⊆ U ∧ (T ` U⊥) ⊆ U⊥ ⟷ (T ∘ (projection U)) = (projection U) ∘ T"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_20: undefined oops


(*
problem_number:6_29
natural language statement:
Suppose $T \in \mathcal{L}(V)$ and $U$ is a subspace of $V$. Prove that $U$ is invariant under $T$ if and only if $U^{\perp}$ is invariant under $T^{*}$.
lean statement:

codex statement:
theorem invariant_of_adjoint_invariant:
  fixes T::"'a::euclidean_space ⇒ 'a" and U::"'a set"
  assumes "linear T" "subspace U"
  shows "U ⊆ carrier T ⟷ (U⊥) ⊆ carrier (adjoint T)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_6_29: undefined oops


(*
problem_number:7_4
natural language statement:
Suppose $P \in \mathcal{L}(V)$ is such that $P^{2}=P$. Prove that $P$ is an orthogonal projection if and only if $P$ is self-adjoint.
lean statement:

codex statement:
theorem orthogonal_projection_iff_self_adjoint:
  fixes P::"'a::euclidean_space ⇒ 'a"
  assumes "linear P" "P^2 = P"
  shows "orthogonal_projection P ⟷ selfadjoint P"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_4: undefined oops


(*
problem_number:7_5
natural language statement:
Show that if $\operatorname{dim} V \geq 2$, then the set of normal operators on $V$ is not a subspace of $\mathcal{L}(V)$.
lean statement:
theorem exercise_7_5 {V : Type*} [inner_product_space ℂ V] 
  [finite_dimensional ℂ V] (hV : finrank V ≥ 2) :
  ∀ U : submodule ℂ (End ℂ V), U.carrier ≠
  {T | T * T.adjoint = T.adjoint * T} :=

codex statement:
theorem normal_operators_not_subspace_of_linear_operators:
  fixes V::"'a::euclidean_space set"
  assumes "DIM('a) ≥ 2"
  shows "∀N. linear N ⟶ normal N ⟶ False"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_5: undefined oops


(*
problem_number:7_6
natural language statement:
Prove that if $T \in \mathcal{L}(V)$ is normal, then $\operatorname{range} T=\operatorname{range} T^{*}.$
lean statement:
theorem exercise_7_6 {V : Type*} [inner_product_space ℂ V]
  [finite_dimensional ℂ V] (T : End ℂ V)
  (hT : T * T.adjoint = T.adjoint * T) :
  T.range = T.adjoint.range :=

codex statement:
theorem range_of_normal_eq_range_of_adjoint:
  fixes T::"'a::euclidean_space ⇒ 'a"
  assumes "linear T" "T adjoint = T"
  shows "range T = range (T adjoint)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_6: undefined oops


(*
problem_number:7_8
natural language statement:
Prove that there does not exist a self-adjoint operator $T \in \mathcal{L}\left(\mathbf{R}^{3}\right)$ such that $T(1,2,3)=(0,0,0)$ and $T(2,5,7)=(2,5,7)$.
lean statement:

codex statement:
theorem not_exists_self_adjoint_operator_of_two_eigenvectors:
  fixes T::"real^3 ⇒ real^3"
  assumes "linear T" "self_adjoint T" "T (vector [1,2,3]) = 0" "T (vector [2,5,7]) = vector [2,5,7]"
  shows False
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_8: undefined oops


(*
problem_number:7_9
natural language statement:
Prove that a normal operator on a complex inner-product space is self-adjoint if and only if all its eigenvalues are real.
lean statement:
theorem exercise_7_9 {V : Type*} [inner_product_space ℂ V]
  [finite_dimensional ℂ V] (T : End ℂ V)
  (hT : T * T.adjoint = T.adjoint * T) :
  is_self_adjoint T ↔ ∀ e : T.eigenvalues, (e : ℂ).im = 0 :=

codex statement:
theorem normal_operator_is_self_adjoint_iff_eigenvalues_are_real:
  fixes A::"'a::euclidean_space ⇒ 'a"
  assumes "normal_operator A"
  shows "self_adjoint A ⟷ (∀x. eigenvalue A x ⟶ x∈ℝ)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_9: undefined oops


(*
problem_number:7_10
natural language statement:
Suppose $V$ is a complex inner-product space and $T \in \mathcal{L}(V)$ is a normal operator such that $T^{9}=T^{8}$. Prove that $T$ is self-adjoint and $T^{2}=T$.
lean statement:
theorem exercise_7_10 {V : Type*} [inner_product_space ℂ V]
  [finite_dimensional ℂ V] (T : End ℂ V)
  (hT : T * T.adjoint = T.adjoint * T) (hT1 : T^9 = T^8) :
  is_self_adjoint T ∧ T^2 = T :=

codex statement:
theorem normal_operator_of_power_eq_power_succ:
  fixes T::"'a::complex_inner_product_space ⇒ 'a"
  assumes "normal T" "T^9 = T^8"
  shows "T = adjoint T ∧ T^2 = T"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_10: undefined oops


(*
problem_number:7_11
natural language statement:
Suppose $V$ is a complex inner-product space. Prove that every normal operator on $V$ has a square root. (An operator $S \in \mathcal{L}(V)$ is called a square root of $T \in \mathcal{L}(V)$ if $S^{2}=T$.)
lean statement:
theorem exercise_7_11 {V : Type*} [inner_product_space ℂ V]
  [finite_dimensional ℂ V] {T : End ℂ V} (hT : T*T.adjoint = T.adjoint*T) :
  ∃ (S : End ℂ V), S ^ 2 = T :=

codex statement:
theorem exists_sqrt_of_normal_operator:
  fixes V::"'a::complex_inner_product_space"
  assumes "normal_operator V"
  shows "∃S. bounded_linear S ∧ S^2 = T"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_11: undefined oops


(*
problem_number:7_14
natural language statement:
Suppose $T \in \mathcal{L}(V)$ is self-adjoint, $\lambda \in \mathbf{F}$, and $\epsilon>0$. Prove that if there exists $v \in V$ such that $\|v\|=1$ and $\|T v-\lambda v\|<\epsilon,$ then $T$ has an eigenvalue $\lambda^{\prime}$ such that $\left|\lambda-\lambda^{\prime}\right|<\epsilon$.
lean statement:
theorem exercise_7_14 {𝕜 V : Type*} [is_R_or_C 𝕜]
  [inner_product_space 𝕜 V] [finite_dimensional 𝕜 V]
  {T : End 𝕜 V} (hT : is_self_adjoint T)
  {l : 𝕜} {ε : ℝ} (he : ε > 0) : ∃ v : V, ∥v∥ = 1 ∧ ∥T v - l • v∥ < ε →
  ∃ l' : T.eigenvalues, ∥l - l'∥ < ε :=

codex statement:
theorem exists_eigenvalue_of_self_adjoint_operator:
  fixes T::"'a::euclidean_space ⇒ 'a"
  assumes "self_adjoint T" "∃v. norm v = 1 ∧ norm (T v - λ v) < ε"
  shows "∃λ'. eigenvalue T λ' ∧ abs (λ - λ') < ε"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_14: undefined oops


(*
problem_number:7_15
natural language statement:
Suppose $U$ is a finite-dimensional real vector space and $T \in$ $\mathcal{L}(U)$. Prove that $U$ has a basis consisting of eigenvectors of $T$ if and only if there is an inner product on $U$ that makes $T$ into a self-adjoint operator.
lean statement:

codex statement:
theorem exists_inner_product_of_eigenvectors_basis:
  fixes T::"'a::euclidean_space ⇒ 'a"
  assumes "linear T" "∃b. independent b ∧ b ⊆ carrier_vec n ∧ span b = carrier_vec n"
  shows "∃B. inner_product_space B ∧ (∀x∈b. eigenvector B T x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_15: undefined oops


(*
problem_number:7_17
natural language statement:
Prove that the sum of any two positive operators on $V$ is positive.
lean statement:

codex statement:
theorem sum_of_positive_operators_is_positive:
  fixes V::"'a::euclidean_space set" and f g::"'a ⇒ 'a"
  assumes "linear f" "linear g" "∀x∈V. 0 ≤ f x ⋅ x" "∀x∈V. 0 ≤ g x ⋅ x"
  shows "∀x∈V. 0 ≤ (f + g) x ⋅ x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_17: undefined oops


(*
problem_number:7_18
natural language statement:
Prove that if $T \in \mathcal{L}(V)$ is positive, then so is $T^{k}$ for every positive integer $k$.
lean statement:

codex statement:
theorem positive_of_positive_power:
  fixes T::"'a::euclidean_space ⇒ 'a"
  assumes "linear T" "positive T"
  shows "positive (T^k)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_18: undefined oops




end