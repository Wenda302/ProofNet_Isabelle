theory "Cambridge-Tripos"
  imports "HOL-Complex_Analysis.Complex_Analysis"

begin

(*
problem_number:2022_IA_1-II-9D-a
natural language statement:
Let $a_{n}$ be a sequence of real numbers. Show that if $a_{n}$ converges, the sequence $\frac{1}{n} \sum_{k=1}^{n} a_{k}$ also converges and $\lim _{n \rightarrow \infty} \frac{1}{n} \sum_{k=1}^{n} a_{k}=\lim _{n \rightarrow \infty} a_{n}$.
lean statement:

codex statement:
theorem lim_sum_div_n_eq_lim:
  fixes f::"nat \<Rightarrow> 'a::real_normed_vector"
  assumes "convergent f"
  shows "convergent (\<lambda>n. (\<Sum>i<n. f i) / n) \<and> lim (\<lambda>n. (\<Sum>i<n. f i) / n) = lim f"
Our comment on the codex statement: type real, not 'a::real_normed_vector
 *)
theorem "exercise_2022_IA_1-II-9D-a":
  fixes a::"nat \<Rightarrow> real"
  assumes "convergent a"
  shows "convergent (\<lambda>n. (\<Sum>i<n. a i) / n) \<and> lim (\<lambda>n. (\<Sum>i<n. a i) / n) = lim a"
  oops

(*
problem_number:2022_IA_1-II-10D-c
natural language statement:
Let a function $g:(0, \infty) \rightarrow \mathbb{R}$ be continuous and bounded. Show that for every $T>0$ there exists a sequence $x_{n}$ such that $x_{n} \rightarrow \infty$ and $\lim _{n \rightarrow \infty}\left(g\left(x_{n}+T\right)-g\left(x_{n}\right)\right)=0 .$
lean statement:

codex statement:
theorem exists_seq_tendsto_infty_of_continuous_bounded:
  fixes g::"real \<Rightarrow> real"
  assumes "continuous_on {0<..} g" "bounded (range g)"
  shows "\<forall>T>0. \<exists>x. x\<longrightarrow>\<infinity> \<and> (\<forall>n. g (x n + T) - g (x n) \<longrightarrow> 0)"
Our comment on the codex statement: the limits are expressed wrongly, especially "x tends to infinity"
 *)
theorem "exercise_2022_IA_1-II-10D-c":
  fixes g::"real \<Rightarrow> real"
  assumes "continuous_on {0<..} g" "bounded (range g)"
  shows "\<forall>T>0. \<exists>x::nat\<Rightarrow>real. filterlim x at_top sequentially \<and> (\<lambda>n. g (x n + T) - g (x n)) \<longlonglongrightarrow> 0"
  oops

(*
problem_number:2022_IA_4-I-1E-a
natural language statement:
By considering numbers of the form $3 p_{1} \ldots p_{k}-1$, show that there are infinitely many primes 
of the form $3 n+2$ with $n \in \mathbb{N}$.
lean statement:

codex statement:
theorem exists_infinite_primes_of_form_3n_plus_2:
  fixes n::nat
  assumes "\<forall>p. prime p \<longrightarrow> p dvd n \<longrightarrow> p = 2 \<or> p = 3"
  shows "\<exists>p. prime p \<and> p dvd n"
Our comment on the codex statement: ALL WRONG. It turned the hint into a (contradictory) assumption!
 *)
theorem "exercise_2022_IA_4-I-1E-a": 
  shows "infinite {p::nat. prime p \<and> (\<exists>n. p = 3*n+2)}"
  oops

(*
problem_number:2022_IA_4-I-2D-a
natural language statement:
Prove that $\sqrt[3]{2}+\sqrt[3]{3}$ is irrational.
lean statement:

codex statement:
theorem irrational_of_sum_of_irrational_roots:
  assumes "\<forall>x y. x^3 = 2 \<and> y^3 = 3 \<longrightarrow> x = y"
  shows "\<forall>x y. x^3 = 2 \<and> y^3 = 3 \<longrightarrow> x + y \<noteq> 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IA_4-I-2D-a":
  shows "root 3 2 + root 3 3 \<notin> \<rat>"
  oops


(*
problem_number:2022_IB_3-II-13G-a-i
natural language statement:
Let $U \subset \mathbb{C}$ be a (non-empty) connected open set and let $f_n$ be a sequence of holomorphic functions defined on $U$. Suppose that $f_n$ converges uniformly to a function $f$ on every compact subset of $U$. Show that $f$ is holomorphic in $U$.
lean statement:

codex statement:
theorem holomorphic_of_uniform_convergent_holomorphic:
  fixes f::"complex \<Rightarrow> complex" and f::"nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes "open U" "connected U" "\<forall>n. holomorphic_on U (f n)" "\<forall>K. compact K \<subseteq> U \<longrightarrow> uniform_limit (f n) f (uniformity_on K)"
  shows "holomorphic_on U f"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2022_IB_3-II-13G-a-i":
  assumes "open U" "connected U" "U \<noteq> {}" 
  assumes "\<forall>n. (f n) holomorphic_on U" and "\<forall>K. compact K \<and> K \<subseteq> U \<longrightarrow> uniform_limit K f F sequentially"
  shows "F holomorphic_on U"
  oops


(*
problem_number:2022_IB_3-II-11G-b
natural language statement:
Let $f: \mathbb{R}^{2} \rightarrow \mathbb{R}^{2}$ be the map given by $f(x, y)=\left(\frac{\cos x+\cos y-1}{2}, \cos x-\cos y\right)$. Prove that $f$ has a fixed point.
lean statement:

codex statement:
theorem exists_fixed_point_of_f:
  fixes f::"real \<Rightarrow> real \<Rightarrow> real"
  assumes "f = (\<lambda>x y. (cos x + cos y - 1)/2, cos x - cos y)"
  shows "\<exists>x. f x = x"
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
  fixes f::"complex \<Rightarrow> complex"
  assumes "f holomorphic_on {z. z \<noteq> 0}" "f 0 = 0"
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
  fixes V::"complex vector" and \<alpha>::"complex \<Rightarrow> complex"
  assumes "finite_dimensional V" "inner_product_space V" "linear \<alpha>" "\<alpha> o \<alpha> = \<alpha> o \<alpha>"
  shows "\<exists>v. v \<noteq> 0 \<and> (\<alpha> v = \<alpha> v) \<and> (\<alpha> v = \<alpha> v)"
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
  shows "finitely_generated R M \<longleftrightarrow> finitely_generated R N \<and> finitely_generated R (quotient_module.quotient N)"
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
  shows "\<exists>K. normal_subgroup K G \<and> card (G / K) dvd card (H / (\<one> H)) \<and> card (G / K) \<ge> card (H / (\<one> H))"
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
  fixes R::"('a::euclidean_space \<Rightarrow> 'b::euclidean_space) ring"
  assumes "continuous_on UNIV f" "continuous_on UNIV g"
  shows "\<exists>I. ideal I R \<and> \<forall>J. ideal J R \<longrightarrow> J \<subseteq> I \<longrightarrow> J = I"
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
  fixes f::"real \<Rightarrow> real"
  assumes "decseq f" "\<forall>x. f x > 0"
  shows "(\<Sum>i<n. f i) \<longrightarrow> \<infinity>"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem "exercise_2018_IA_1-I-3E-b": undefined oops




end
