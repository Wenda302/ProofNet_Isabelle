theory Herstein
 imports "HOL-Algebra.Algebra"
begin

(*
problem_number:2_1_18
natural language statement:
If $G$ is a finite group of even order, show that there must be an element $a \neq e$ such that $a=a^{-1}$.
lean statement:
theorem exercise_2_1_18 {G : Type*} [group G]
  [fintype G] (hG2 : even (fintype.card G)) :
  \<exists> (a : G), a \<noteq> \<one> \<and> a = inv a :=

codex statement:
theorem exists_inv_eq_of_even_order:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite (carrier G)" "order G mod 2 = 0"
  shows "\<exists>a\<in>carrier G. a \<noteq> \<one> \<and> a = inv a"
Our comment on the codex statement: pretty good but needs a locale context, like most of the others
 *)
theorem (in group) exercise_2_1_18:
  assumes "finite (carrier G)" "order G mod 2 = 0"
  shows "\<exists>a\<in>carrier G. a \<noteq> \<one> \<and> a = inv a"
  oops


(*
problem_number:2_1_21
natural language statement:
Show that a group of order 5 must be abelian.
lean statement:
theorem exercise_2_1_21 (G : Type* ) [group G] [fintype G]
  (hG : card G = 5) :
  comm_group G :=

codex statement:
theorem abelian_of_order_5:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 5"
  shows "abelian G"
Our comment on the codex statement: "abelian" is undefined (use comm_group)
 *)
theorem (in group) exercise_2_1_21:
  assumes "group G" "order G = 5"
  shows "comm_group G"
  oops


(*
problem_number:2_1_26
natural language statement:
If $G$ is a finite group, prove that, given $a \in G$, there is a positive integer $n$, depending on $a$, such that $a^n = e$.
lean statement:
theorem exercise_2_1_26 {G : Type*} [group G]
  [fintype G] (a : G) : \<exists> (n : \<nat>), a ^ n = \<one> :=

codex statement:
theorem exists_nat_pow_eq_one_of_finite_group:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite (carrier G)"
  shows "\<exists>n. a [^] n = \<one>"
Our comment on the codex statement: Needs locale group; also n needs to be positive
 *)
theorem (in group) exercise_2_1_26:
  assumes "finite (carrier G)"
  shows "\<exists>n>0. a [^] n = \<one>"
  oops


(*
problem_number:2_1_27
natural language statement:
If $G$ is a finite group, prove that there is an integer $m > 0$ such that $a^m = e$ for all $a \in G$.
lean statement:
theorem exercise_2_1_27 {G : Type*} [group G]
  [fintype G] : \<exists> (m : \<nat>), \<forall> (a : G), a ^ m = \<one> :=

codex statement:
theorem exists_nat_pow_eq_one_of_finite_group:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite (carrier G)"
  shows "\<exists>m::nat. \<forall>a\<in>carrier G. a [^] m = \<one>"
Our comment on the codex statement: Needs locale group; also m needs to be positive
 *)
theorem (in group) exercise_2_1_27:
  assumes "finite (carrier G)"
  shows "\<exists>m>0. \<forall>a\<in>carrier G. a [^] m = \<one>"
  oops

(*
problem_number:2_2_3
natural language statement:
If $G$ is a group in which $(a b)^{i}=a^{i} b^{i}$ for three consecutive integers $i$, prove that $G$ is abelian.
lean statement:
theorem exercise_2_2_3 {G : Type*} [group G]
  {P : \<nat> \<rightarrow> Prop} {hP : P = \<lambda> i, \<forall> a b : G, (a*b)^i = a^i * b^i}
  (hP1 : \<exists> n : \<nat>, P n \<and> P (n+1) \<and> P (n+2)) : comm_group G :=

codex statement:
theorem abelian_of_consecutive_powers_eq:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "\<forall>a b. (a * b) [^] (i::nat) = a [^] i * b [^] i" "i+1\<in>{i, i+1, i+2}"
  shows "comm_group G"
Our comment on the codex statement: the English version is ambiguous and the codex version is scrambled
 *)
theorem (in group) exercise_2_2_3:
  defines "P \<equiv> \<lambda>i::nat. \<forall>a b. (a \<otimes> b) [^] i = a [^] i \<otimes> b [^] i"
  assumes "P i" "P(Suc i)" "P(Suc(Suc i))"
  shows "comm_group G"
  oops

(*
problem_number:2_2_5
natural language statement:
Let $G$ be a group in which $(a b)^{3}=a^{3} b^{3}$ and $(a b)^{5}=a^{5} b^{5}$ for all $a, b \in G$. Show that $G$ is abelian.
lean statement:
theorem exercise_2_2_5 {G : Type*} [group G]
  (h : \<forall> (a b : G), (a * b) ^ 3 = a ^ 3 * b ^ 3 \<and> (a * b) ^ 5 = a ^ 5 * b ^ 5) :
  comm_group G :=

codex statement:
theorem abelian_of_power_eq_power:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "\<forall>a b. (a * b)^3 = a^3 * b^3" "\<forall>a b. (a * b)^5 = a^5 * b^5"
  shows "comm_group G"
Our comment on the codex statement: good but needs the group locale
 *)
theorem (in group) exercise_2_2_5:
  defines "P \<equiv> \<lambda>i::nat. \<forall>a b. (a \<otimes> b) [^] i = a [^] i \<otimes> b [^] i"
  assumes "P 3" "P 5"
  shows "comm_group G"
  oops


(*
problem_number:2_2_6c
natural language statement:
Let $G$ be a group in which $(a b)^{n}=a^{n} b^{n}$ for some fixed integer $n>1$ for all $a, b \in G$. 
For all $a, b \in G$, prove that $\left(a b a^{-1} b^{-1}\right)^{n(n-1)}=e$.
lean statement:
theorem exercise_2_2_6c {G : Type*} [group G] {n : \<nat>} (hn : n > 1)
  (h : \<forall> (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  \<forall> (a b : G), (a * b * inv a * inv b) ^ (n * (n - 1)) = 1 :=

codex statement:
theorem power_of_commutator_eq_one:
  fixes G::"('a, 'b) monoid_scheme" (structure) and a b::'a
  assumes "group G" "\<forall>a b. (a * b) [^] n = a [^] n * b [^] n" "n > 1"
  shows "(a * b * a [^] -1 * b [^] -1) [^] (n * (n - 1)) = \<one>"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem (in group) exercise_2_2_6c:
  assumes "\<forall>a b. (a \<otimes> b) [^] n = a [^] n \<otimes> b [^] n" and "n > 1"
  shows "(a \<otimes> b \<otimes> inv a \<otimes> inv b) [^] (n * (n - 1)) = \<one>"
  oops


(*
problem_number:2_3_17
natural language statement:
If $G$ is a group and $a, x \in G$, prove that $C\left(x^{-1} a x\right)=x^{-1} C(a) x$
lean statement:
theorem exercise_2_3_17 {G : Type*} [has_mul G] [group G] (a x : G) :
  set.centralizer {inv x*a*x} =
  (\<lambda> g : G, inv x*g*x) '' (set.centralizer {a}) :=

codex statement:
theorem conjugate_of_conjugate_eq_conjugate:
  fixes G::"('a, 'b) monoid_scheme" (structure) and a x::'a
  assumes "group G"
  shows "conjugate x (conjugate x a) = conjugate x a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_3_17: undefined oops


(*
problem_number:2_3_19
natural language statement:
If $M$ is a subgroup of $G$ such that $x^{-1} M x \subset M$ for all $x \in G$, prove that actually $x^{-1} M x=M$.
lean statement:
theorem exercise_2_3_19 {G : Type*} [group G] {M : subgroup G}
  (hM : \<forall> (x : G), (\<lambda> g : G, inv x*g*x) '' M \<subset> M) :
  \<forall> x : G, (\<lambda> g : G, inv x*g*x) '' M = M :=

codex statement:
theorem subgroup_of_conjugate_subset_is_conjugate:
  fixes G::"('a, 'b) monoid_scheme" (structure) and M::"'a set"
  assumes "group G" "subgroup M G" "\<forall>x\<in>carrier G. inv x * M * x \<subseteq> M"
  shows "\<forall>x\<in>carrier G. inv x * M * x = M"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_3_19: undefined oops


(*
problem_number:2_3_16
natural language statement:
If a group $G$ has no proper subgroups, prove that $G$ is cyclic of order $p$, where $p$ is a prime number.
lean statement:
theorem exercise_2_3_16 {G : Type*} [group G]
  (hG : \<forall> H : subgroup G, H = \<top> \<or> H = \<bot>) :
  is_cyclic G \<and> \<exists> (p : \<nat>) (fin : fintype G), nat.prime p \<and> @card G fin = p :=

codex statement:
theorem cyclic_of_prime_order_of_no_proper_subgroups:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "\<forall>H. subgroup H G \<rightarrow> H = G \<or> H = {\<one>}"
  shows "\<exists>p. prime p \<and> order G = p"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_3_16: undefined oops


(*
problem_number:2_3_21
natural language statement:
If $A, B$ are subgroups of $G$ such that $b^{-1} Ab \subset A$ for all $b \in B$, show that $AB$ is a subgroup of $G$.
lean statement:

codex statement:
theorem subgroup_of_subgroup_conjugate_subset:
  fixes A B::"'a::group_add set"
  assumes "subgroup A G" "subgroup B G" "\<forall>b\<in>B. inv b * A * b \<subseteq> A"
  shows "subgroup (A + B) G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_3_21: undefined oops


(*
problem_number:2_3_22
natural language statement:
If $A$ and $B$ are finite subgroups, of orders $m$ and $n$, respectively, of the abelian group $G$, prove that $AB$ is a subgroup of order $mn$ if $m$ and $n$ are relatively prime.
lean statement:

codex statement:
theorem order_of_product_of_finite_subgroups_is_product_of_orders:
  fixes A B::"'a::group_add set"
  assumes "finite A" "finite B" "subgroup A G" "subgroup B G" "\<forall>x\<in>A. \<forall>y\<in>B. x+y\<in>A \<or> x+y\<in>B"
  shows "card (A+B) = card A * card B"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_3_22: undefined oops


(*
problem_number:2_3_28
natural language statement:
Let $M, N$ be subgroups of $G$ such that $x^{-1}Mx \subset M$ and $x^{-1} N x \subset N$ for all $x \in G$. Prove that $MN$ is a subgroup of $G$ and that $x^{-1} (MN)x \subset MN$ for all $x \in G$.
lean statement:

codex statement:
theorem subgroup_of_conjugate_subgroups:
  fixes G::"('a, 'b) monoid_scheme" (structure) and M N::"'a set"
  assumes "group G" "subgroup M G" "subgroup N G" "\<forall>x\<in>G. inv x * M * x \<subseteq> M" "\<forall>x\<in>G. inv x * N * x \<subseteq> N"
  shows "subgroup (M * N) G" "\<forall>x\<in>G. inv x * (M * N) * x \<subseteq> M * N"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_3_28: undefined oops


(*
problem_number:2_3_29
natural language statement:
If $M$ is a subgroup of $G$ such that $x^{-1}Mx \subset M$ for all $x \in G$, prove that actually $x^{-1}Mx = M$.
lean statement:

codex statement:
theorem subgroup_of_conjugate_subset_is_conjugate:
  fixes G::"('a, 'b) monoid_scheme" (structure) and M::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "subgroup M G" "\<forall>x\<in>carrier G. inv x * M * x \<subseteq> M"
  shows "\<forall>x\<in>carrier G. inv x * M * x = M"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_3_29: undefined oops


(*
problem_number:2_4_8
natural language statement:
If every right coset of $H$ in $G$ is a left coset of $H$ in $G$, prove that $aHa^{-1} = H$ for all $a \in G$.
lean statement:

codex statement:
theorem right_coset_eq_left_coset_of_H_in_G_of_all_a_in_G:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) submonoid" (structure)
  assumes "group G" "subgroup H G" "\<forall>a\<in>carrier G. right_coset H a = left_coset H a"
  shows "\<forall>a\<in>carrier G. a * H * inv a = H"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_8: undefined oops


(*
problem_number:2_4_26
natural language statement:
Let $G$ be a group, $H$ a subgroup of $G$, and let $S$ be the set of all distinct right cosets of $H$ in $G$, $T$ the set of all left cosets of $H$ in $G$. Prove that there is a 1-1 mapping of $S$ onto $T$.
lean statement:

codex statement:
theorem exists_bijective_of_right_left_cosets:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) submonoid" (structure)
  assumes "group G" "subgroup H G"
  shows "\<exists>f. bij_betw f (right_cosets H G) (left_cosets H G)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_26: undefined oops


(*
problem_number:2_4_32
natural language statement:
Let $G$ be a finite group, $H$ a subgroup of $G$. Let $f(a)$ be the least positive $m$ such that $a^m \in H$. Prove that $f(a) \mid o(a)$, where $o(a)$ is an order of $a$.
lean statement:

codex statement:
theorem order_of_element_divides_order_of_subgroup:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "subgroup H G" "finite_group G" "a \<in> carrier G"
  shows "order G a ∣ order H a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_32: undefined oops


(*
problem_number:2_4_36
natural language statement:
If $a > 1$ is an integer, show that $n \mid \varphi(a^n - 1)$, where $\phi$ is the Euler $\varphi$-function.
lean statement:
theorem exercise_2_4_36 {a n : \<nat>} (h : a > 1) :
  n ∣ (a ^ n - 1).totient :=

codex statement:
theorem divides_phi_of_int_succ_one_power_int_sub_one:
  fixes a::int
  assumes "a > 1"
  shows "\<forall>n::nat. n ∣ phi (a^n - 1)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_36: undefined oops


(*
problem_number:2_5_6
natural language statement:
Prove that if $\varphi \colon G \rightarrow G'$ is a homomorphism, then $\varphi(G)$, the image of $G$, is a subgroup of $G'$.
lean statement:

codex statement:
theorem image_of_homomorphism_is_subgroup:
  fixes G G'::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "group G'" "\<forall>x y. \<exists>z. z \<in> carrier G \<and> \<exists>z'. z' \<in> carrier G' \<and> f z = z' \<and> f (x * y) = f x * f y"
  shows "subgroup (f ` carrier G) G'"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5_6: undefined oops


(*
problem_number:2_5_23
natural language statement:
Let $G$ be a group such that all subgroups of $G$ are normal in $G$. If $a, b \in G$, prove that $ba = a^jb$ for some $j$.
lean statement:
theorem exercise_2_5_23 {G : Type*} [group G]
  (hG : \<forall> (H : subgroup G), H.normal) (a b : G) :
  \<exists> (j : \<int>) , b*a = a^j * b:=

codex statement:
theorem exists_j_of_subgroup_normal:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "\<forall>H. subgroup H G \<rightarrow> normal_subgroup H G" "a \<in> carrier G" "b \<in> carrier G"
  shows "\<exists>j. b * a = a [^] j * b"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5_23: undefined oops


(*
problem_number:2_5_30
natural language statement:
Suppose that $|G| = pm$, where $p \nmid m$ and $p$ is a prime. If $H$ is a normal subgroup of order $p$ in $G$, prove that $H$ is characteristic.
lean statement:
theorem exercise_2_5_30 {G : Type*} [group G] [fintype G]
  {p m : \<nat>} (hp : nat.prime p) (hp1 : \<not> p ∣ m) (hG : card G = p*m)
  {H : subgroup G} [fintype H] [H.normal] (hH : card H = p):
  characteristic H :=

codex statement:
theorem characteristic_of_order_prime_power_div_order_prime:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "group H" "order G = p * m" "prime p" "p ∣ m" "order H = p" "H \<subseteq> G" "normal G H"
  shows "char G H"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5_30: undefined oops


(*
problem_number:2_5_31
natural language statement:
Suppose that $G$ is an abelian group of order $p^nm$ where $p \nmid m$ is a prime.  If $H$ is a subgroup of $G$ of order $p^n$, prove that $H$ is a characteristic subgroup of $G$.
lean statement:
theorem exercise_2_5_31 {G : Type*} [comm_group G] [fintype G]
  {p m n : \<nat>} (hp : nat.prime p) (hp1 : \<not> p ∣ m) (hG : card G = p^n*m)
  {H : subgroup G} [fintype H] (hH : card H = p^n) :
  characteristic H :=

codex statement:
theorem characteristic_of_abelian_group_of_order_p_power_n_times_m:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "abelian_group G" "order G = p^n * m" "prime p" "coprime m p" "order H = p^n" "subgroup H G"
  shows "char_subgroup H G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5_31: undefined oops


(*
problem_number:2_5_37
natural language statement:
If $G$ is a nonabelian group of order 6, prove that $G \simeq S_3$.
lean statement:
theorem exercise_2_5_37 (G : Type* ) [group G] [fintype G]
  (hG : card G = 6) (hG' : is_empty (comm_group G)) :
  G ≅ equiv.perm (fin 3) :=

codex statement:
theorem nonabelian_group_of_order_6_is_isomorphic_to_S3:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 6" "\<not> abelian G"
  shows "G ≅ (permutations (UNIV::'a set))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5_37: undefined oops


(*
problem_number:2_5_43
natural language statement:
Prove that a group of order 9 must be abelian.
lean statement:
theorem exercise_2_5_43 (G : Type* ) [group G] [fintype G]
  (hG : card G = 9) :
  comm_group G :=

codex statement:
theorem abelian_of_order_9:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 9"
  shows "abelian G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5_43: undefined oops


(*
problem_number:2_5_44
natural language statement:
Prove that a group of order $p^2$, $p$ a prime, has a normal subgroup of order $p$.
lean statement:
theorem exercise_2_5_44 {G : Type*} [group G] [fintype G] {p : \<nat>}
  (hp : nat.prime p) (hG : card G = p^2) :
  \<exists> (N : subgroup G) (fin : fintype N), @card N fin = p \<and> N.normal :=

codex statement:
theorem exists_normal_subgroup_of_order_prime_power:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = p^2" "normalization_semidom_class.prime p"
  shows "\<exists>H. subgroup H G \<and> order H = p"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5_44: undefined oops


(*
problem_number:2_5_52
natural language statement:
Let $G$ be a finite group and $\varphi$ an automorphism of $G$ such that $\varphi(x) = x^{-1}$ for more than three-fourths of the elements of $G$. Prove that $\varphi(y) = y^{-1}$ for all $y \in G$, and so $G$ is abelian.
lean statement:
theorem exercise_2_5_52 {G : Type*} [group G] [fintype G]
  (\<phi> : G \<cong>* G) {I : finset G} (hI : \<forall> x \<in> I, \<phi> x = inv x)
  (hI1 : 0.75 * card G \<le> card I) :
  \<forall> x : G, \<phi> x = inv x \<and> \<forall> x y : G, x*y = y*x :=

codex statement:
theorem abelian_of_inverse_of_automorphism_of_finite_group:
  fixes G::"'a::group_add monoid"
  assumes "finite (carrier G)" "\<exists>\<phi>. automorphism G \<phi> \<and> (\<forall>x\<in>carrier G. \<phi> x = inv x)"
  shows "abelian G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_5_52: undefined oops


(*
problem_number:2_6_15
natural language statement:
If $G$ is an abelian group and if $G$ has an element of order $m$ and one of order $n$, where $m$ and $n$ are relatively prime, prove that $G$ has an element of order $mn$.
lean statement:
theorem exercise_2_6_15 {G : Type*} [comm_group G] {m n : \<nat>}
  (hm : \<exists> (g : G), order_of g = m)
  (hn : \<exists> (g : G), order_of g = n)
  (hmn : m.coprime n) :
  \<exists> (g : G), order_of g = m * n :=

codex statement:
theorem exists_element_of_order_mul_of_relatively_prime:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "\<forall>n ::nat. x [^] n \<noteq> \<one>" "\<forall>n ::nat. y [^] n \<noteq> \<one>" "coprime m n"
  shows "\<exists>z. z [^] (m*n) = \<one>"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_6_15: undefined oops


(*
problem_number:2_7_3
natural language statement:
Let $G$ be the group of nonzero real numbers under multiplication and let $N = \{1, -1\}$. Prove that $G / N \simeq$ positive real numbers under multiplication.
lean statement:

codex statement:
theorem quotient_group_of_nonzero_real_numbers_isomorphic_positive_real_numbers:
  shows "group_isomorphism (quotient_group (nonzero_real_numbers::real monoid) {1, -1}) (positive_real_numbers::real monoid)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_7_3: undefined oops


(*
problem_number:2_7_7
natural language statement:
If $\varphi$ is a homomorphism of $G$ onto $G'$ and $N \triangleleft G$, show that $\varphi(N) \triangleleft G'$.
lean statement:
theorem exercise_2_7_7 {G : Type*} [group G] {G' : Type*} [group G']
  (\<phi> : G \<rightarrow>* G') (N : subgroup G) [N.normal] :
  (map \<phi> N).normal  :=

codex statement:
theorem normal_of_homomorphism_image:
  fixes G G'::"('a, 'b) monoid_scheme" (structure) and \<phi>::"'a ⇒ 'a"
  assumes "group G" "group G'" "homomorphism G G' \<phi>" "normal_subgroup N G"
  shows "normal_subgroup (\<phi> '' N) G'"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_7_7: undefined oops


(*
problem_number:2_8_7
natural language statement:
If $G$ is a group with subgroups $A, B$ of orders $m, n$, respectively, where $m$ and $n$ are relatively prime, prove that the subset of $G$, $AB = \{ab \mid a \in A, b \in B\}$, has $mn$ distinct elements.
lean statement:

codex statement:
theorem card_prod_of_subgroups_eq_mul_card_of_subgroups:
  fixes G::"('a, 'b) monoid_scheme" (structure) and A B::"'a set"
  assumes "group G" "subgroup A G" "subgroup B G" "coprime (card A) (card B)"
  shows "card (A * B) = card A * card B"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_8_7: undefined oops


(*
problem_number:2_8_12
natural language statement:
Prove that any two nonabelian groups of order 21 are isomorphic.
lean statement:
theorem exercise_2_8_12 {G H : Type*} [fintype G] [fintype H]
  [group G] [group H] (hG : card G = 21) (hH : card H = 21)
  (hG1 : is_empty(comm_group G)) (hH1 : is_empty (comm_group H)) :
  G \<cong>* H :=

codex statement:
theorem isomorphic_of_nonabelian_order_21:
  fixes G H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "group H" "order G = 21" "order H = 21" "\<not> abelian_group G" "\<not> abelian_group H"
  shows "G \<cong> H"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_8_12: undefined oops


(*
problem_number:2_8_15
natural language statement:
Prove that if $p > q$ are two primes such that $q \mid p - 1$, then any two nonabelian groups of order $pq$ are isomorphic.
lean statement:
theorem exercise_2_8_15 {G H: Type*} [fintype G] [group G] [fintype H]
  [group H] {p q : \<nat>} (hp : nat.prime p) (hq : nat.prime q)
  (h : p > q) (h1 : q ∣ p - 1) (hG : card G = p*q) (hH : card G = p*q) :
  G \<cong>* H :=

codex statement:
theorem isomorphic_of_prime_divides_prime_minus_one:
  fixes p q::nat
  assumes "prime p" "prime q" "q > p" "q dvd p - 1"
  shows "\<forall>G H. group G \<and> group H \<and> order G = p * q \<and> order H = p * q \<rightarrow> G \<cong> H"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_8_15: undefined oops


(*
problem_number:2_9_2
natural language statement:
If $G_1$ and $G_2$ are cyclic groups of orders $m$ and $n$, respectively, prove that $G_1 \times G_2$ is cyclic if and only if $m$ and $n$ are relatively prime.
lean statement:
theorem exercise_2_9_2 {G H : Type*} [fintype G] [fintype H] [group G]
  [group H] (hG : is_cyclic G) (hH : is_cyclic H) :
  is_cyclic (G \<times> H) \<Longrightarrow> (card G).coprime (card H) :=

codex statement:
theorem cyclic_of_relatively_prime:
  fixes G1 G2::"('a, 'b) monoid_scheme" (structure)
  assumes "group G1" "group G2" "cyclic G1" "cyclic G2" "\<forall>x\<in>carrier G1. \<forall>y\<in>carrier G2. order x = order y \<rightarrow> x = \<one> \<and> y = \<one>"
  shows "cyclic (G1 \<times> G2)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_9_2: undefined oops


(*
problem_number:2_10_1
natural language statement:
Let $A$ be a normal subgroup of a group $G$, and suppose that $b \in G$ is an element of prime order $p$, and that $b \not\in A$. Show that $A \cap (b) = (e)$.
lean statement:
theorem exercise_2_10_1 {G : Type*} [group G] (A : subgroup G)
  [A.normal] {b : G} (hp : nat.prime (order_of b)) :
  A ⊓ (closure {b}) = \<bot> :=

codex statement:
theorem trivial_intersection_of_prime_order_element_and_normal_subgroup:
  fixes G::"('a, 'b) monoid_scheme" (structure) and A::"'a set"
  assumes "group G" "normal_subgroup G A" "prime (order b)" "b ∉ A"
  shows "A ∩ (carrier (⟦b⟧)) = {\<one>}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_10_1: undefined oops


(*
problem_number:2_11_6
natural language statement:
If $P$ is a $p$-Sylow subgroup of $G$ and $P \triangleleft G$, prove that $P$ is the only $p$-Sylow subgroup of $G$.
lean statement:
theorem exercise_2_11_6 {G : Type*} [group G] {p : \<nat>} (hp : nat.prime p)
  {P : sylow p G} (hP : P.normal) :
  \<forall> (Q : sylow p G), P = Q :=

codex statement:
theorem sylow_subgroup_of_normal_subgroup_is_unique:
  fixes p::nat and G::"('a, 'b) monoid_scheme" (structure)
  assumes "normalization_semidom_class.prime p" "group G" "order G = (p^a) * m" "finite (carrier G)" "subgroup P G" "card P = p^a" "P \<subseteq> carrier G" "P \<subseteq> normalizer G P"
  shows "\<forall>Q. subgroup Q G \<and> card Q = p^a \<rightarrow> Q = P"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_11_6: undefined oops


(*
problem_number:2_11_7
natural language statement:
If $P \triangleleft G$, $P$ a $p$-Sylow subgroup of $G$, prove that $\varphi(P) = P$ for every automorphism $\varphi$ of $G$.
lean statement:
theorem exercise_2_11_7 {G : Type*} [group G] {p : \<nat>} (hp : nat.prime p)
  {P : sylow p G} (hP : P.normal) :
  characteristic (P : subgroup G) :=

codex statement:
theorem phi_of_sylow_is_sylow:
  fixes G::"('a, 'b) monoid_scheme" (structure) and P::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "normalization_semidom_class.prime p" "p_group P" "p_group G" "p_group.is_Sylow p P G" "group_hom G G \<phi>"
  shows "group_hom P P \<phi>"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_11_7: undefined oops


(*
problem_number:2_11_22
natural language statement:
Show that any subgroup of order $p^{n-1}$ in a group $G$ of order $p^n$ is normal in $G$.
lean statement:
theorem exercise_2_11_22 {p : \<nat>} {n : \<nat>} {G : Type*} [fintype G]
  [group G] (hp : nat.prime p) (hG : card G = p ^ n) {K : subgroup G}
  [fintype K] (hK : card K = p ^ (n-1)) :
  K.normal :=

codex statement:
theorem normal_of_order_p_pow_n_minus_1_of_order_p_pow_n:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = p^n" "subgroup H G" "order H = p^(n-1)"
  shows "normal H G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_11_22: undefined oops


(*
problem_number:3_2_21
natural language statement:
If $\sigma, \tau$ are two permutations that disturb no common element and $\sigma \tau = e$, prove that $\sigma = \tau = e$.
lean statement:
theorem exercise_3_2_21 {\<alpha> : Type*} [fintype \<alpha>] {\<sigma> \<tau>: equiv.perm \<alpha>}
  (h1 : \<forall> a : \<alpha>, \<sigma> a = a \<Longrightarrow> \<tau> a \<noteq> a) (h2 : \<tau> ∘ \<sigma> = id) :
  \<sigma> = 1 \<and> \<tau> = 1 :=

codex statement:
theorem permutation_of_disturb_no_common_eq_id_eq_id:
  fixes \<sigma>::"'a ⇒ 'a" and \<tau>::"'a ⇒ 'a"
  assumes "permutation \<sigma>" "permutation \<tau>" "\<forall>x. \<sigma> x \<noteq> x \<rightarrow> \<tau> x \<noteq> x" "\<sigma> ∘ \<tau> = id"
  shows "\<sigma> = id \<and> \<tau> = id"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_2_21: undefined oops


(*
problem_number:3_2_23
natural language statement:
Let $\sigma, \tau$ be two permutations such that they both have decompositions into disjoint cycles of cycles of lengths $m_1, m_2, \ldots, m_k$. Prove that for some permutation $\beta, \tau = \beta \sigma \beta^{-1}$.
lean statement:

codex statement:
theorem exists_permutation_eq_permutation_comp_permutation_inv:
  fixes \<sigma>::"'a perm" and \<tau>::"'a perm"
  assumes "\<sigma> permutes {1..n}" "\<tau> permutes {1..n}" "\<sigma> = (∏i\<in>{1..n}. (\<sigma> i))" "\<tau> = (∏i\<in>{1..n}. (\<tau> i))"
  shows "\<exists>\<beta>. \<tau> = \<beta> ∘ \<sigma> ∘ inv \<beta>"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_2_23: undefined oops


(*
problem_number:3_3_2
natural language statement:
If $\sigma$ is a $k$-cycle, show that $\sigma$ is an odd permutation if $k$ is even, and is an even permutation if $k$ is odd.
lean statement:

codex statement:
theorem even_permutation_of_even_cycle:
  fixes \<sigma>::"'a::finite perm"
  assumes "\<sigma> = (a⇩R b⇩R c⇩R d⇩R e⇩R f⇩R g⇩R h⇩R i⇩R j⇩R k⇩R l⇩R m⇩R n⇩R o⇩R p⇩R q⇩R r⇩R s⇩R t⇩R u⇩R v⇩R w⇩R x⇩R y⇩R z⇩R)"
  shows "evenperm \<sigma>"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_3_2: undefined oops


(*
problem_number:3_3_9
natural language statement:
If $n \geq 5$ and $(e) \neq N \subset A_n$ is a normal subgroup of $A_n$, show that $N$ must contain a 3-cycle.
lean statement:

codex statement:
theorem exists_three_cycle_of_normal_subgroup_of_An:
  fixes n::nat and N::"'a set"
  assumes "n ≥ 5" "group_set A_n" "N \<subseteq> carrier A_n" "normal_subgroup A_n N" "N \<noteq> {𝟙}"
  shows "\<exists>a b c. a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> a \<and> (a, b, c) \<in> N"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_3_9: undefined oops


(*
problem_number:4_1_19
natural language statement:
Show that there is an infinite number of solutions to $x^2 = -1$ in the quaternions.
lean statement:
theorem exercise_4_1_19 : infinite {x : quaternion \<real> | x^2 = -1} :=

codex statement:
theorem infinite_solutions_of_quaternion_square_eq_neg_one:
  fixes x::"'a::real_normed_algebra_1"
  assumes "x^2 = -1"
  shows "\<exists>y. y^2 = -1 \<and> y \<noteq> x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_1_19: undefined oops


(*
problem_number:4_1_28
natural language statement:
Show that $\{x \in R \mid \det x \neq O\}$ forms a group, $G$, under matrix multiplication and that $N = \{x \in R \mid \det x = 1\}$ is a normal subgroup of $G$.
lean statement:

codex statement:
theorem det_neq_zero_is_group:
  fixes R::"('a::{comm_ring_1,ring_no_zero_divisors}^'n) set"
  assumes "\<forall>x\<in>R. det x \<noteq> 0"
  shows "group R"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_1_28: undefined oops


(*
problem_number:4_1_29
natural language statement:
If $x \in R$ is a zero-divisor, show that $\det x = 0$, and, conversely, if $x \neq 0$ is such that $\det x = 0$, then $x$ is a zero-divisor in $R$.
lean statement:

codex statement:
theorem det_eq_zero_of_zero_divisor:
  fixes x::"'a::{comm_ring_1, ring_no_zero_divisors}"
  assumes "x \<noteq> 0" "\<exists>y. y \<noteq> 0 \<and> x * y = 0"
  shows "det x = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_1_29: undefined oops


(*
problem_number:4_1_34
natural language statement:
Let $T$ be the group of matrices $A$ with entries in the field $\mathbb{Z}_2$ such that $\det A$ is not equal to 0. Prove that $T$ is isomorphic to $S_3$, the symmetric group of degree 3.
lean statement:
theorem exercise_4_1_34 : equiv.perm (fin 3) \<cong>* general_linear_group (fin 2) (zmod 2) :=

codex statement:
theorem isomorphic_to_symmetric_group_of_degree_3:
  fixes T::"int matrix set"
  assumes "T = {A. det A \<noteq> 0}"
  shows "T \<cong> (permutations_of_set (UNIV::'a::finite set))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_1_34: undefined oops


(*
problem_number:4_2_5
natural language statement:
Let $R$ be a ring in which $x^3 = x$ for every $x \in R$. Prove that $R$ is commutative.
lean statement:
theorem exercise_4_2_5 {R : Type*} [ring R]
  (h : \<forall> x : R, x ^ 3 = x) : comm_ring R :=

codex statement:
theorem commutative_of_cube_eq_id:
  fixes R::"'a::ring_1"
  assumes "\<forall>x. x^3 = x"
  shows "comm_ring R"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_2_5: undefined oops


(*
problem_number:4_2_6
natural language statement:
If $a^2 = 0$ in $R$, show that $ax + xa$ commutes with $a$.
lean statement:
theorem exercise_4_2_6 {R : Type*} [ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (x + x * a) * a :=

codex statement:
theorem commutes_of_square_zero:
  fixes a x::"'a::ring"
  assumes "a^2 = 0"
  shows "a * x + x * a = a * (x + x)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_2_6: undefined oops


(*
problem_number:4_2_9
natural language statement:
Let $p$ be an odd prime and let $1 + \frac{1}{2} + ... + \frac{1}{p - 1} = \frac{a}{b}$, where $a, b$ are integers. Show that $p \mid a$.
lean statement:
theorem exercise_4_2_9 {p : \<nat>} (hp : nat.prime p) (hp1 : odd p) :
  \<exists> (a b : \<int>), a / b = \<Sum> i in finset.range p, 1 / (i + 1) \<rightarrow>  UP p ∣ a :=

codex statement:
theorem prime_divides_a_of_sum_frac_eq_frac_a_b:
  fixes p::nat and a b::int
  assumes "prime p" "p > 2" "\<Sum>i=1..p-1. 1/(of_nat i) = of_int a / of_int b"
  shows "p dvd a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_2_9: undefined oops


(*
problem_number:4_3_1
natural language statement:
If $R$ is a commutative ring and $a \in R$, let $L(a) = \{x \in R \mid xa = 0\}$. Prove that $L(a)$ is an ideal of $R$.
lean statement:
theorem exercise_4_3_1 {R : Type*} [comm_ring R] (a : R) :
  \<exists> I : ideal R, {x : R | x*a=0} = I :=

codex statement:
theorem ideal_of_left_zero_of_commutative_ring:
  fixes R::"'a::comm_ring_1"
  assumes "a\<in>R"
  shows "ideal R (left_zero_of R a)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_3_1: undefined oops


(*
problem_number:4_3_4
natural language statement:
If $I, J$ are ideals of $R$, define $I + J$ by $I + J = {i + j \mid i \in I, j \in J}$. Prove that $I + J$ is an ideal of $R$.
lean statement:

codex statement:
theorem sum_ideals_is_ideal:
  fixes R::"'a::comm_ring_1 ring" and I J::"'a set"
  assumes "ideal R I" "ideal R J"
  shows "ideal R (I + J)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_3_4: undefined oops


(*
problem_number:4_3_25
natural language statement:
Let $R$ be the ring of $2 \times 2$ matrices over the real numbers; suppose that $I$ is an ideal of $R$. Show that $I = (0)$ or $I = R$.
lean statement:
theorem exercise_4_3_25 (I : ideal (matrix (fin 2) (fin 2) \<real>)) :
  I = \<bot> \<or> I = \<top> :=

codex statement:
theorem ideal_of_2x2_matrix_ring_is_zero_or_ring:
  fixes R::"real mat"
  assumes "ideal R I"
  shows "I = {0} \<or> I = carrier R"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_3_25: undefined oops


(*
problem_number:4_4_9
natural language statement:
Show that $(p - 1)/2$ of the numbers $1, 2, \ldots, p - 1$ are quadratic residues and $(p - 1)/2$ are quadratic nonresidues $\mod p$.
lean statement:
theorem exercise_4_4_9 (p : \<nat>) (hp : nat.prime p) :
  \<exists> S : finset (zmod p), S.card = (p-1)/2 \<and> \<exists> x : zmod p, x^2 = p \<and>
  \<exists> S : finset (zmod p), S.card = (p-1)/2 \<and> \<not> \<exists> x : zmod p, x^2 = p :=

codex statement:
theorem quadratic_residues_and_nonresidues_mod_p:
  fixes p::nat
  assumes "prime p"
  shows "card {x. x < p \<and> x^2 ≡ 1 [MOD p]} = (p - 1) div 2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4_9: undefined oops


(*
problem_number:4_5_12
natural language statement:
If $F \subset K$ are two fields and $f(x), g(x) \in F[x]$ are relatively prime in $F[x]$, show that they are relatively prime in $K[x]$.
lean statement:

codex statement:
theorem relatively_prime_of_relatively_prime_in_subfield:
  fixes F::"'a::field_char_0" and K::"'a::field_char_0"
  assumes "F \<subseteq> K" "poly_relprime F f g"
  shows "poly_relprime K f g"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_12: undefined oops


(*
problem_number:4_5_16
natural language statement:
Let $F = \mathbb{Z}_p$ be the field of integers $\mod p$, where $p$ is a prime, and let $q(x) \in F[x]$ be irreducible of degree $n$. Show that $F[x]/(q(x))$ is a field having at exactly $p^n$ elements.
lean statement:
theorem exercise_4_5_16 {p n: \<nat>} (hp : nat.prime p)
  {q : polynomial (zmod p)} (hq : irreducible q) (hn : q.degree = n) :
  \<exists> is_fin : fintype $ polynomial (zmod p) ⧸ ideal.span ({q} : set (polynomial $ zmod p)),
  @card (polynomial (zmod p) ⧸ ideal.span {q}) is_fin = p ^ n \<and>
  is_field (polynomial $ zmod p):=

codex statement:
theorem card_of_quotient_ring_eq_pow_prime:
  fixes p::nat and q::"nat ⇒ nat"
  assumes "prime p" "irreducible q" "degree q = n"
  shows "card (quotient_ring (poly_ring p) q) = p^n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_16: undefined oops


(*
problem_number:4_5_23
natural language statement:
Let $F = \mathbb{Z}_7$ and let $p(x) = x^3 - 2$ and $q(x) = x^3 + 2$ be in $F[x]$. Show that $p(x)$ and $q(x)$ are irreducible in $F[x]$ and that the fields $F[x]/(p(x))$ and $F[x]/(q(x))$ are isomorphic.
lean statement:
theorem exercise_4_5_23 {p q: polynomial (zmod 7)}
  (hp : p = X^3 - 2) (hq : q = X^3 + 2) :
  irreducible p \<and> irreducible q \<and>
  (nonempty $ polynomial (zmod 7) ⧸ ideal.span ({p} : set $ polynomial $ zmod 7) \<cong>+*
  polynomial (zmod 7) ⧸ ideal.span ({q} : set $ polynomial $ zmod 7)) :=

codex statement:
theorem isomorphic_of_irreducible_polynomial:
  fixes p q::"int poly"
  assumes "irreducible p" "irreducible q" "degree p = degree q"
  shows "ring_hom_ring.quotient_ring_isomorphic (poly_ring \<int>) p q"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_23: undefined oops


(*
problem_number:4_5_25
natural language statement:
If $p$ is a prime, show that $q(x) = 1 + x + x^2 + \cdots x^{p - 1}$ is irreducible in $Q[x]$.
lean statement:
theorem exercise_4_5_25 {p : \<nat>} (hp : nat.prime p) :
  irreducible (\<Sum> i : finset.range p, X ^ p : polynomial \<rat>) :=

codex statement:

Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_25: undefined oops


(*
problem_number:4_6_2
natural language statement:
Prove that $f(x) = x^3 + 3x + 2$ is irreducible in $Q[x]$.
lean statement:
theorem exercise_4_6_2 : irreducible (X^3 + 3*X + 2 : polynomial \<rat>) :=

codex statement:
theorem irreducible_of_polynomial:
  fixes f::"real ⇒ real"
  assumes "f = (\<lambda>x. x^3 + 3*x + 2)"
  shows "irreducible (polynomial f)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_6_2: undefined oops


(*
problem_number:4_6_3
natural language statement:
Show that there is an infinite number of integers a such that $f(x) = x^7 + 15x^2 - 30x + a$ is irreducible in $Q[x]$.
lean statement:
theorem exercise_4_6_3 :
  infinite {a : \<int> | irreducible (X^7 + 15*X^2 - 30*X + a : polynomial \<rat>)} :=

codex statement:
theorem infinite_irreducible_polynomial_of_degree_7:
  fixes a::int
  assumes "\<forall>x. x^7 + 15*x^2 - 30*x + a \<noteq> 0"
  shows "\<exists>a. irreducible (poly_of_int a)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_6_3: undefined oops


(*
problem_number:5_1_8
natural language statement:
If $F$ is a field of characteristic $p \neq 0$, show that $(a + b)^m = a^m + b^m$, where $m = p^n$, for all $a, b \in F$ and any positive integer $n$.
lean statement:
theorem exercise_5_1_8 {p m n: \<nat>} {F : Type*} [field F]
  (hp : nat.prime p) (hF : char_p F p) (a b : F) (hm : m = p ^ n) :
  (a + b) ^ m = a^m + b^m :=

codex statement:
theorem sum_power_eq_sum_power_of_char_neq_zero:
  fixes F::"'a::field" and a b::'a and m::nat
  assumes "characteristic F \<noteq> 0" "m = characteristic F ^ n" "n > 0"
  shows "(a + b)^m = a^m + b^m"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_1_8: undefined oops


(*
problem_number:5_2_20
natural language statement:
Let $V$ be a vector space over an infinite field $F$. Show that $V$ cannot be the set-theoretic union of a finite number of proper subspaces of $V$.
lean statement:
theorem exercise_5_2_20 {F V I: Type*} [infinite F] [field F]
  [add_comm_group V] [module F V] {u : I \<rightarrow> submodule F V}
  (hu : \<forall> i : I, u i \<noteq> \<top>) :
  (\<Union> i : I, (u i : set V)) \<noteq> \<top> :=

codex statement:
theorem not_union_of_finite_proper_subspaces:
  fixes V::"'a::{field, infinite} set"
  assumes "finite S" "S \<subseteq> Pow V" "\<forall>X\<in>S. X \<subset> V" "\<forall>X\<in>S. X \<noteq> V" "\<Union>S = V"
  shows False
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_2_20: undefined oops


(*
problem_number:5_3_7
natural language statement:
If $a \in K$ is such that $a^2$ is algebraic over the subfield $F$ of $K$, show that a is algebraic over $F$.
lean statement:
theorem exercise_5_3_7 {K : Type*} [field K] {F : subfield K}
  {a : K} (ha : is_algebraic F (a ^ 2)) : is_algebraic F a :=

codex statement:
theorem algebraic_of_algebraic_square:
  fixes a::"'a::{field_char_0,algebra_1}"
  assumes "algebraic K a^2"
  shows "algebraic K a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_3_7: undefined oops


(*
problem_number:5_3_10
natural language statement:
Prove that $\cos 1^{\circ}$  is algebraic over $\mathbb{Q}$.
lean statement:
theorem exercise_5_3_10 : is_algebraic \<rat> (cos (real.pi / 180)) :=

codex statement:
theorem cos_one_degree_is_algebraic:
  shows "algebraic (cos (1::real))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_3_10: undefined oops


(*
problem_number:5_4_3
natural language statement:
If $a \in C$ is such that $p(a) = 0$, where $p(x) = x^5 + \sqrt{2}x^3 + \sqrt{5}x^2 + \sqrt{7}x + \sqrt{11}$, show that $a$ is algebraic over $\mathbb{Q}$ of degree at most 80.
lean statement:
theorem exercise_5_4_3 {a : \<complex>} {p : \<complex> \<rightarrow> \<complex>}
  (hp : p = \<lambda> x, x^5 + real.sqrt 2 * x^3 + real.sqrt 5 * x^2 +
  real.sqrt 7 * x + 11)
  (ha : p a = 0) :
  \<exists> p : polynomial \<complex> , p.degree < 80 \<and> a \<in> p.roots \<and>
  \<forall> n : p.support, \<exists> a b : \<int>, p.coeff n = a / b :=

codex statement:
theorem exists_poly_of_degree_leq_80:
  fixes a::complex
  assumes "poly p a = 0" "degree p = 5" "\<forall>x. poly p x \<noteq> 0"
  shows "\<exists>q. degree q \<le> 80 \<and> poly q a = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_4_3: undefined oops


(*
problem_number:5_5_2
natural language statement:
Prove that $x^3 - 3x - 1$ is irreducible over $\mathbb{Q}$.
lean statement:
theorem exercise_5_5_2 : irreducible (X^3 - 3*X - 1 : polynomial \<rat>) :=

codex statement:
theorem irreducible_of_polynomial_over_Q:
  fixes x::"real poly"
  assumes "degree x = 3" "\<forall>x. x^3 - 3*x - 1 = 0 \<rightarrow> x = 1 \<or> x = -1"
  shows "irreducible x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_5_2: undefined oops


(*
problem_number:5_6_3
natural language statement:
Let $\mathbb{Q}$ be the rational field and let $p(x) = x^4 + x^3 + x^2 + x + 1$.  Show that there is an extension $K$ of $Q$ with $[K:Q] = 4$ over which $p(x)$ splits into linear factors.
lean statement:

codex statement:
theorem exists_splitting_field_of_polynomial_over_rational_field:
  fixes p::"complex poly"
  assumes "p = [:1, 1, 1, 1, 1:]"
  shows "\<exists>K. algebraic_closure K = K \<and> K \<subseteq> \<complex> \<and> (\<exists>f. degree f = 4 \<and> f dvd p \<and> irreducible f \<and> (\<exists>g. degree g = 1 \<and> g dvd f))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_6_3: undefined oops


(*
problem_number:5_6_14
natural language statement:
If $F$ is of characteristic $p \neq 0$, show that all the roots of $x^m - x$, where $m = p^n$, are distinct.
lean statement:
theorem exercise_5_6_14 {p m n: \<nat>} (hp : nat.prime p) {F : Type*}
  [field F] [char_p F p] (hm : m = p ^ n) :
  card (root_set (X ^ m - X : polynomial F) F) = m :=

codex statement:
theorem distinct_roots_of_x_pow_m_minus_x:
  fixes F::"'a::field" and m::nat
  assumes "characteristic F \<noteq> 0" "m = characteristic F ^ n"
  shows "\<forall>x y. x \<noteq> y \<rightarrow> x^m \<noteq> y^m"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_6_14: undefined oops




end
