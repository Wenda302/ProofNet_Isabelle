theory "Dummit-Foote"
 imports Main
begin

(*
problem_number:1_1_2a
natural language statement:
Prove the the operation $\star$ on $\mathbb{Z}$ defined by $a\star b=a-b$ is not commutative.
lean statement:
theorem exercise_1_1_2a : ∃ a b : ℤ, a - b ≠ b - a :=
begin
  use [0, 1]
end

codex statement:
theorem not_commutative_of_star_on_int:
  fixes a b::int
  shows "a ∗ b ≠ b ∗ a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_2a: undefined oops


(*
problem_number:1_1_3
natural language statement:
Prove that the addition of residue classes $\mathbb{Z}/n\mathbb{Z}$ is associative.
lean statement:
theorem exercise_1_1_3 (n : ℤ) : 
  ∀ (a b c : ℤ), (a+b)+c ≡ a+(b+c) [ZMOD n] :=
begin 
  intros a b c, 
  ring_nf
end

codex statement:
theorem add_assoc_of_residue_classes:
  fixes n::nat
  assumes "n>0"
  shows "∀x y z. (x + y) mod n + z mod n = (x + y + z) mod n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_3: undefined oops


(*
problem_number:1_1_4
natural language statement:
Prove that the multiplication of residue class $\mathbb{Z}/n\mathbb{Z}$ is associative.
lean statement:
theorem exercise_1_1_4 (n : ℕ) : 
  ∀ (a b c : ℕ), (a * b) * c ≡ a * (b * c) [ZMOD n] :=
begin 
  intros a b c, 
  ring_nf, 
end

codex statement:
theorem mult_assoc_of_residue_class:
  fixes n::nat
  assumes "n>0"
  shows "∀x y z. (x::int) mod n * (y mod n) * (z mod n) = (x * y * z) mod n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_4: undefined oops


(*
problem_number:1_1_5
natural language statement:
Prove that for all $n>1$ that $\mathbb{Z}/n\mathbb{Z}$ is not a group under multiplication of residue classes.
lean statement:
theorem exercise_1_1_5 (n : ℕ) (hn : 1 < n) : 
  is_empty (group (zmod n)) := 

codex statement:
theorem not_group_of_Z_mod_n_mult:
  fixes n::nat
  assumes "n>1"
  shows "∀x∈carrier (Z_mod_n). ∃y∈carrier (Z_mod_n). x * y ≠ 𝟙"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_5: undefined oops


(*
problem_number:1_1_15
natural language statement:
Prove that $(a_1a_2\dots a_n)^{-1} = a_n^{-1}a_{n-1}^{-1}\dots a_1^{-1}$ for all $a_1, a_2, \dots, a_n\in G$.
lean statement:
theorem exercise_1_1_15 {G : Type*} [group G] (as : list G) :
  as.prod⁻¹ = (as.reverse.map (λ x, x⁻¹)).prod :=
begin 
  simp only [list.prod_hom _, list.map_reverse, list.prod_reverse],
  induction as generalizing, 
  simp, 
  simp *, 
end

codex statement:
theorem inverse_of_prod_eq_prod_inverse:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G"
  shows "∀v. (∏i∈v. f i)⁻¹ = ∏i∈v. (f i)⁻¹"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_15: undefined oops


(*
problem_number:1_1_16
natural language statement:
Let $x$ be an element of $G$. Prove that $x^2=1$ if and only if $|x|$ is either $1$ or $2$.
lean statement:
theorem exercise_1_1_16 {G : Type*} [group G] 
  (x : G) (hx : x ^ 2 = 1) :
  order_of x = 1 ∨ order_of x = 2 :=

codex statement:
theorem order_eq_one_or_two_of_square_eq_one:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "x^2 = 𝟭"
  shows "order x = 1 ∨ order x = 2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_16: undefined oops


(*
problem_number:1_1_17
natural language statement:
Let $x$ be an element of $G$. Prove that if $|x|=n$ for some positive integer $n$ then $x^{-1}=x^{n-1}$.
lean statement:
theorem exercise_1_1_17 {G : Type*} [group G] {x : G} {n : ℕ}
  (hxn: order_of x = n) :
  x⁻¹ = x ^ (n-1) :=

codex statement:
theorem inverse_eq_power_of_order_minus_one:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order x = n" "n>0"
  shows "x⁻¹ = x [^] (n-1)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_17: undefined oops


(*
problem_number:1_1_18
natural language statement:
Let $x$ and $y$ be elements of $G$. Prove that $xy=yx$ if and only if $y^{-1}xy=x$ if and only if $x^{-1}y^{-1}xy=1$.
lean statement:
theorem exercise_1_1_18 {G : Type*} [group G]
  (x y : G) : x * y = y * x ↔ y⁻¹ * x * y = x ↔ x⁻¹ * y⁻¹ * x * y = 1 :=

codex statement:
theorem commutative_iff_inverse_commutative_iff_inverse_commutative_inverse:
  fixes x y::"'a::group_add"
  shows "x * y = y * x ⟷ y⁻¹ * x * y = x ⟷ x⁻¹ * y⁻¹ * x * y = 𝟭"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_18: undefined oops


(*
problem_number:1_1_20
natural language statement:
For $x$ an element in $G$ show that $x$ and $x^{-1}$ have the same order.
lean statement:
theorem exercise_1_1_20 {G : Type*} [group G] {x : G} :
  order_of x = order_of x⁻¹ :=

codex statement:
theorem order_of_inverse_eq_order:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "x ∈ carrier G"
  shows "order G x = order G (x⁻¹)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_20: undefined oops


(*
problem_number:1_1_22a
natural language statement:
If $x$ and $g$ are elements of the group $G$, prove that $|x|=\left|g^{-1} x g\right|$.
lean statement:
theorem exercise_1_1_22a {G : Type*} [group G] (x g : G) :
  order_of x = order_of (g⁻¹ * x * g) :=

codex statement:
theorem order_of_conjugate_eq_order:
  fixes G::"('a, 'b) monoid_scheme" (structure) and x g::'a
  assumes "group G" "x ∈ carrier G" "g ∈ carrier G"
  shows "order G x = order G (g⁻¹ * x * g)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_22a: undefined oops


(*
problem_number:1_1_22b
natural language statement:
Deduce that $|a b|=|b a|$ for all $a, b \in G$.
lean statement:
theorem exercise_1_1_22b {G: Type*} [group G] (a b : G) : 
  order_of (a * b) = order_of (b * a) :=

codex statement:
theorem abs_mult_eq_abs_mult:
  fixes a b::"'a::{comm_ring_1,ring_char_0}"
  shows "abs (a * b) = abs (b * a)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_22b: undefined oops


(*
problem_number:1_1_25
natural language statement:
Prove that if $x^{2}=1$ for all $x \in G$ then $G$ is abelian.
lean statement:
theorem exercise_1_1_25 {G : Type*} [group G] 
  (h : ∀ x : G, x ^ 2 = 1) : ∀ a b : G, a*b = b*a :=

codex statement:
theorem abelian_of_square_eq_one:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "∀x∈carrier G. x^2 = 𝟭"
  shows "abelian G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_25: undefined oops


(*
problem_number:1_1_29
natural language statement:
Prove that $A \times B$ is an abelian group if and only if both $A$ and $B$ are abelian.
lean statement:
theorem exercise_1_1_29 {A B : Type*} [group A] [group B] :
  ∀ x y : A × B, x*y = y*x ↔ (∀ x y : A, x*y = y*x) ∧ 
  (∀ x y : B, x*y = y*x) :=

codex statement:
theorem abelian_of_prod_abelian:
  fixes A B::"'a::group_add"
  assumes "abelian_group A" "abelian_group B"
  shows "abelian_group (A × B)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_29: undefined oops


(*
problem_number:1_1_34
natural language statement:
If $x$ is an element of infinite order in $G$, prove that the elements $x^{n}, n \in \mathbb{Z}$ are all distinct.
lean statement:
theorem exercise_1_1_34 {G : Type*} [group G] {x : G} 
  (hx_inf : order_of x = 0) (n m : ℤ) :
  x ^ n ≠ x ^ m :=

codex statement:
theorem distinct_powers_of_infinite_order_element:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "∀n ::nat. x [^] n ≠ 𝟭"
  shows "∀ m n :: int. m ≠ n ⟶ x [^] m ≠ x [^] n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_1_34: undefined oops


(*
problem_number:1_3_8
natural language statement:
Prove that if $\Omega=\{1,2,3, \ldots\}$ then $S_{\Omega}$ is an infinite group
lean statement:
theorem exercise_1_3_8 : infinite (equiv.perm ℕ) :=

codex statement:
theorem infinite_of_permutation_group:
  fixes Ω::"nat set"
  assumes "finite Ω"
  shows "infinite (permutation_group Ω)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_3_8: undefined oops


(*
problem_number:1_6_4
natural language statement:
Prove that the multiplicative groups $\mathbb{R}-\{0\}$ and $\mathbb{C}-\{0\}$ are not isomorphic.
lean statement:
theorem exercise_1_6_4 : 
  is_empty (multiplicative ℝ ≃* multiplicative ℂ) :=

codex statement:
theorem not_isomorphic_of_real_complex:
  shows "∀f::real ⇒ complex. (∀x y. f (x * y) = f x * f y) ⟶ (∃x. f x = 0)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_6_4: undefined oops


(*
problem_number:1_6_11
natural language statement:
Let $A$ and $B$ be groups. Prove that $A \times B \cong B \times A$.
lean statement:
theorem exercise_1_6_11 {A B : Type*} [group A] [group B] : 
  A × B ≃* B × A :=

codex statement:
theorem isomorphic_of_prod_commute:
  fixes A B::"('a, 'b) monoid_scheme"
  assumes "group A" "group B"
  shows "A × B ≅ B × A"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_6_11: undefined oops


(*
problem_number:1_6_17
natural language statement:
Let $G$ be any group. Prove that the map from $G$ to itself defined by $g \mapsto g^{-1}$ is a homomorphism if and only if $G$ is abelian.
lean statement:
theorem exercise_1_6_17 {G : Type*} [group G] (f : G → G) 
  (hf : f = λ g, g⁻¹) :
  ∀ x y : G, f x * f y = f (x*y) ↔ ∀ x y : G, x*y = y*x :=   

codex statement:
theorem is_homomorphism_of_inverse_iff_abelian:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G"
  shows "∀x y. (x * y)⁻¹ = y⁻¹ * x⁻¹ ⟷ comm_group G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_6_17: undefined oops


(*
problem_number:1_6_23
natural language statement:
Let $G$ be a finite group which possesses an automorphism $\sigma$ such that $\sigma(g)=g$ if and only if $g=1$. If $\sigma^{2}$ is the identity map from $G$ to $G$, prove that $G$ is abelian.
lean statement:
theorem exercise_1_6_23 {G : Type*} 
  [group G] (σ : mul_aut G) (hs : ∀ g : G, σ g = 1 → g = 1) 
  (hs2 : ∀ g : G, σ (σ g) = g) :
  ∀ x y : G, x*y = y*x :=

codex statement:
theorem abelian_of_automorphism_sigma_sigma_square_eq_id:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite_group G" "∃σ. automorphism G σ" "∀g. g ∈ carrier G ⟶ (σ g = g ⟷ g = 𝟭)" "∀g. g ∈ carrier G ⟶ σ (σ g) = g"
  shows "abelian_group G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_6_23: undefined oops


(*
problem_number:1_7_5
natural language statement:
Prove that the kernel of an action of the group $G$ on a set $A$ is the same as the kernel of the corresponding permutation representation $G\to S_A$.
lean statement:

codex statement:
theorem kernel_of_action_eq_kernel_of_permutation_representation:
  fixes G::"('a, 'b) monoid_scheme" (structure) and A::"'c set"
  assumes "group G" "finite A"
  shows "kernel (λx. permutation_of_list (action G x A)) = kernel (λx. action G x A)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_7_5: undefined oops


(*
problem_number:1_7_6
natural language statement:
Prove that a group $G$ acts faithfully on a set $A$ if and only if the kernel of the action is the set consisting only of the identity.
lean statement:

codex statement:
theorem faithful_action_iff_kernel_eq_singleton:
  fixes G::"('a, 'b) monoid_scheme" (structure) and A::"'c set"
  assumes "group G" "finite A"
  shows "faithful_action G A ⟷ kernel G A = {𝟭}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_1_7_6: undefined oops


(*
problem_number:2_1_5
natural language statement:
Prove that $G$ cannot have a subgroup $H$ with $|H|=n-1$, where $n=|G|>2$.
lean statement:
theorem exercise_2_1_5 {G : Type*} [group G] [fintype G] 
  (hG : card G > 2) (H : subgroup G) [fintype H] : 
  card H ≠ card G - 1 :=

codex statement:
theorem no_subgroup_of_order_n_minus_one:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G > 2"
  shows "∀H. subgroup H G ⟶ order H ≠ order G - 1"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_1_5: undefined oops


(*
problem_number:2_1_13
natural language statement:
Let $H$ be a subgroup of the additive group of rational numbers with the property that $1 / x \in H$ for every nonzero element $x$ of $H$. Prove that $H=0$ or $\mathbb{Q}$.
lean statement:
theorem exercise_2_1_13 (H : add_subgroup ℚ) {x : ℚ} 
  (hH : x ∈ H → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ :=

codex statement:
theorem subgroup_of_rat_with_inv_is_zero_or_rat:
  fixes H::"rat set"
  assumes "subgroup H (add_monoid rat)" "∀x∈H. x ≠ 0 ⟶ inverse x ∈ H"
  shows "H = {0} ∨ H = UNIV"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_1_13: undefined oops


(*
problem_number:2_4_4
natural language statement:
Prove that if $H$ is a subgroup of $G$ then $H$ is generated by the set $H-\{1\}$.
lean statement:
theorem exercise_2_4_4 {G : Type*} [group G] (H : subgroup G) : 
  subgroup.closure ((H : set G) \ {1}) = ⊤ :=

codex statement:
theorem subgroup_generated_by_subtract_one:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "subgroup H G"
  shows "H = ⟦H - {𝟭 G}⟧"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_4: undefined oops


(*
problem_number:2_4_13
natural language statement:
Prove that the multiplicative group of positive rational numbers is generated by the set $\left\{\frac{1}{p} \mid \text{$p$ is a prime} \right\}$.
lean statement:

codex statement:
theorem generated_by_inverse_primes:
  fixes p::"nat ⇒ bool"
  assumes "∀x y. p x ⟶ p y ⟶ p (x*y)" "∀x. p x ⟶ x≥2"
  shows "subgroup_generated (carrier (multiplicative ℚ)) {inverse (of_nat x) | x. p x} = carrier (multiplicative ℚ)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_13: undefined oops


(*
problem_number:2_4_16a
natural language statement:
A subgroup $M$ of a group $G$ is called a maximal subgroup if $M \neq G$ and the only subgroups of $G$ which contain $M$ are $M$ and $G$. Prove that if $H$ is a proper subgroup of the finite group $G$ then there is a maximal subgroup of $G$ containing $H$.
lean statement:
theorem exercise_2_4_16a {G : Type*} [group G] {H : subgroup G}  
  (hH : H ≠ ⊤) : 
  ∃ M : subgroup G, M ≠ ⊤ ∧
  ∀ K : subgroup G, M ≤ K → K = M ∨ K = ⊤ ∧ 
  H ≤ M :=

codex statement:
theorem exists_maximal_subgroup_of_finite_group_containing_proper_subgroup:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite_group G" "subgroup H G" "H ≠ G"
  shows "∃M. maximal_subgroup M G ∧ subgroup H M"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_16a: undefined oops


(*
problem_number:2_4_16b
natural language statement:
Show that the subgroup of all rotations in a dihedral group is a maximal subgroup.
lean statement:
theorem exercise_2_4_16b {n : ℕ} {hn : n ≠ 0} 
  {R : subgroup (dihedral_group n)} 
  (hR : R = subgroup.closure {dihedral_group.r 1}) : 
  R ≠ ⊤ ∧ 
  ∀ K : subgroup (dihedral_group n), R ≤ K → K = R ∨ K = ⊤ :=

codex statement:
theorem maximal_of_rotations_in_dihedral:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "∃n. order G = 2*n"
  shows "∃H. subgroup H G ∧ ∀H'. subgroup H' G ⟶ H = H' ∨ H ∩ H' = {𝟭}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_16b: undefined oops


(*
problem_number:2_4_16c
natural language statement:
Show that if $G=\langle x\rangle$ is a cyclic group of order $n \geq 1$ then a subgroup $H$ is maximal if and only $H=\left\langle x^{p}\right\rangle$ for some prime $p$ dividing $n$.
lean statement:
theorem exercise_2_4_16c {n : ℕ} (H : add_subgroup (zmod n)) : 
  ∃ p : ℕ, nat.prime p ∧ H = add_subgroup.closure {p} ↔ 
  H ≠ ⊤ ∧ ∀ K : add_subgroup (zmod n), H ≤ K → K = H ∨ K = ⊤ := 

codex statement:
theorem maximal_subgroup_of_cyclic_group_is_prime_power:
  fixes G::"('a, 'b) monoid_scheme" (structure) and x::'a
  assumes "group G" "x ∈ carrier G" "order G = n" "n ≥ 1" "cyclic G" "subgroup H G" "maximal_eq_exists_not_subgroup H G"
  shows "∃p. prime p ∧ p dvd n ∧ H = ⟦{x [^] p}⟧"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_2_4_16c: undefined oops


(*
problem_number:3_1_3a
natural language statement:
Let $A$ be an abelian group and let $B$ be a subgroup of $A$. Prove that $A / B$ is abelian.
lean statement:
theorem exercise_3_1_3a {A : Type*} [comm_group A] (B : subgroup A) :
  ∀ a b : A ⧸ B, a*b = b*a :=

codex statement:
theorem quotient_group_of_abelian_group_is_abelian:
  fixes A::"('a, 'b) monoid_scheme" (structure) and B::"('a, 'b) monoid_scheme" (structure)
  assumes "group A" "group B" "subgroup B A" "abelian_group A"
  shows "abelian_group (quotient_group A B)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_1_3a: undefined oops


(*
problem_number:3_1_22a
natural language statement:
Prove that if $H$ and $K$ are normal subgroups of a group $G$ then their intersection $H \cap K$ is also a normal subgroup of $G$.
lean statement:
theorem exercise_3_1_22a (G : Type* ) [group G] (H K : subgroup G) 
  [subgroup.normal H] [subgroup.normal K] :
  subgroup.normal (H ⊓ K) :=

codex statement:
theorem normal_subgroup_of_intersection_of_normal_subgroups:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H K::"'a set"
  assumes "group G" "normal_subgroup H G" "normal_subgroup K G"
  shows "normal_subgroup (H ∩ K) G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_1_22a: undefined oops


(*
problem_number:3_1_22b
natural language statement:
Prove that the intersection of an arbitrary nonempty collection of normal subgroups of a group is a normal subgroup (do not assume the collection is countable).
lean statement:
theorem exercise_3_1_22b {G : Type*} [group G] (I : Type* )
  (H : I → subgroup G) (hH : ∀ i : I, subgroup.normal (H i)) : 
  subgroup.normal (⨅ (i : I), H i):=

codex statement:
theorem normal_subgroup_of_intersection_of_normal_subgroups:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "∀H∈S. normal_subgroup H G" "S ≠ {}"
  shows "normal_subgroup (⋂S) G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_1_22b: undefined oops


(*
problem_number:3_2_8
natural language statement:
Prove that if $H$ and $K$ are finite subgroups of $G$ whose orders are relatively prime then $H \cap K=1$.
lean statement:
theorem exercise_3_2_8 {G : Type*} [group G] (H K : subgroup G)
  [fintype H] [fintype K] 
  (hHK : nat.coprime (fintype.card H) (fintype.card K)) : 
  H ⊓ K = ⊥ :=

codex statement:
theorem finite_subgroups_of_relatively_prime_orders_have_trivial_intersection:
  fixes H K::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite_group H" "finite_group K" "subgroup H G" "subgroup K G" "coprime (order H) (order K)"
  shows "H ∩ K = {𝟭}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_2_8: undefined oops


(*
problem_number:3_2_11
natural language statement:
Let $H \leq K \leq G$. Prove that $|G: H|=|G: K| \cdot|K: H|$ (do not assume $G$ is finite).
lean statement:
theorem exercise_3_2_11 {G : Type*} [group G] {H K : subgroup G}
  (hHK : H ≤ K) : 
  H.index = K.index * H.relindex K :=

codex statement:
theorem index_of_subgroup_mul_index_of_subgroup_of_subgroup:
  fixes G H K::"'a::group_mult"
  assumes "subgroup H G" "subgroup K G" "subgroup H K"
  shows "index G H = index G K * index K H"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_2_11: undefined oops


(*
problem_number:3_2_16
natural language statement:
Use Lagrange's Theorem in the multiplicative group $(\mathbb{Z} / p \mathbb{Z})^{\times}$to prove Fermat's Little Theorem: if $p$ is a prime then $a^{p} \equiv a(\bmod p)$ for all $a \in \mathbb{Z}$.
lean statement:
theorem exercise_3_2_16 (p : ℕ) (hp : nat.prime p) (a : ℕ) :
  nat.coprime a p → a ^ p ≡ a [ZMOD p] :=

codex statement:
theorem fermat_little_theorem:
  fixes p::nat and a::int
  assumes "prime p"
  shows "a mod p = a mod p"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_2_16: undefined oops


(*
problem_number:3_2_21a
natural language statement:
Prove that $\mathbb{Q}$ has no proper subgroups of finite index.
lean statement:
theorem exercise_3_2_21a (H : add_subgroup ℚ) (hH : H ≠ ⊤) : H.index = 0 :=

codex statement:
theorem no_proper_subgroup_of_finite_index:
  fixes G::"'a::group_add set"
  assumes "subgroup G ℚ" "finite_index ℚ G"
  shows "G = ℚ"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_2_21a: undefined oops


(*
problem_number:3_3_3
natural language statement:
Prove that if $H$ is a normal subgroup of $G$ of prime index $p$ then for all $K \leq G$ either $K \leq H$, or $G=H K$ and $|K: K \cap H|=p$.
lean statement:
theorem exercise_3_3_3 {p : primes} {G : Type*} [group G] 
  {H : subgroup G} [hH : H.normal] (hH1 : H.index = p) : 
  ∀ K : subgroup G, K ≤ H ∨ H ⊔ K = ⊤ ∨ (K ⊓ H).relindex K = p :=

codex statement:
theorem prime_index_of_normal_subgroup_of_subgroup:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "group H" "normal_subgroup H G" "prime (card (G / H))" "subgroup K G"
  shows "K ≤ H ∨ (G = H * K ∧ card (K / (K ∩ H)) = card (G / H))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_3_3: undefined oops


(*
problem_number:3_4_1
natural language statement:
Prove that if $G$ is an abelian simple group then $G \cong Z_{p}$ for some prime $p$ (do not assume $G$ is a finite group).
lean statement:
theorem exercise_3_4_1 (G : Type* ) [comm_group G] [is_simple_group G] :
    is_cyclic G ∧ ∃ G_fin : fintype G, nat.prime (@card G G_fin) :=

codex statement:
theorem abelian_simple_group_is_cyclic_group:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "simple_group G" "abelian_group G"
  shows "∃p::nat. ∃(f::'a ⇒ 'a). ∀x y. f (x * y) = f x * f y ∧ f (x * y) = f x * f y ∧ ∀x. f x ≠ 𝟭 ∧ ∀x. f (f x) = 𝟭"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_4_1: undefined oops


(*
problem_number:3_4_4
natural language statement:
Use Cauchy's Theorem and induction to show that a finite abelian group has a subgroup of order $n$ for each positive divisor $n$ of its order.
lean statement:
theorem exercise_3_4_4 {G : Type*} [comm_group G] [fintype G] {n : ℕ}
    (hn : n ∣ (fintype.card G)) :
    ∃ (H : subgroup G) (H_fin : fintype H), @card H H_fin = n  :=

codex statement:
theorem exists_subgroup_of_order_divisor:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite (carrier G)" "abelian G" "n dvd order G" "n > 0"
  shows "∃H. subgroup H G ∧ order H = n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_4_4: undefined oops


(*
problem_number:3_4_5a
natural language statement:
Prove that subgroups of a solvable group are solvable.
lean statement:
theorem exercise_3_4_5a {G : Type*} [group G] 
  (H : subgroup G) [is_solvable G] : is_solvable H :=

codex statement:
theorem subgroup_of_solvable_is_solvable:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "solvable G"
  shows "∀H. subgroup H G ⟶ solvable H"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_4_5a: undefined oops


(*
problem_number:3_4_5b
natural language statement:
Prove that quotient groups of a solvable group are solvable.
lean statement:
theorem exercise_3_4_5b {G : Type*} [group G] [is_solvable G] 
  (H : subgroup G) [subgroup.normal H] : 
  is_solvable (G ⧸ H) :=

codex statement:
theorem solvable_of_quotient_solvable:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "solvable G"
  shows "∀H. subgroup H G ⟶ solvable (G/H)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_4_5b: undefined oops


(*
problem_number:3_4_11
natural language statement:
Prove that if $H$ is a nontrivial normal subgroup of the solvable group $G$ then there is a nontrivial subgroup $A$ of $H$ with $A \unlhd G$ and $A$ abelian.
lean statement:
theorem exercise_3_4_11 {G : Type*} [group G] [is_solvable G] 
  {H : subgroup G} (hH : H ≠ ⊥) [H.normal] : 
  ∃ A ≤ H, A.normal ∧ ∀ a b : A, a*b = b*a :=

codex statement:
theorem exists_abelian_normal_subgroup_of_nontrivial_normal_subgroup:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "solvable_group G" "normal_subgroup H G" "H ≠ {𝟭}"
  shows "∃A. normal_subgroup A G ∧ A ≠ {𝟭} ∧ abelian_group A"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_3_4_11: undefined oops


(*
problem_number:4_2_8
natural language statement:
Prove that if $H$ has finite index $n$ then there is a normal subgroup $K$ of $G$ with $K \leq H$ and $|G: K| \leq n!$.
lean statement:
theorem exercise_4_2_8 {G : Type*} [group G] {H : subgroup G} 
  {n : ℕ} (hn : n > 0) (hH : H.index = n) : 
  ∃ K ≤ H, K.normal ∧ K.index ≤ n.factorial :=

codex statement:
theorem exists_normal_subgroup_of_finite_index_leq_factorial:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "group H" "H ≤ G" "finite_index G H"
  shows "∃K. normal_subgroup K G ∧ K ≤ H ∧ finite_index G K ∧ card (quotient_group.quotient G K) ≤ fact (card (quotient_group.quotient G H))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_2_8: undefined oops


(*
problem_number:4_2_9a
natural language statement:
Prove that if $p$ is a prime and $G$ is a group of order $p^{\alpha}$ for some $\alpha \in \mathbb{Z}^{+}$, then every subgroup of index $p$ is normal in $G$.
lean statement:
theorem exercise_4_2_9a {G : Type*} [fintype G] [group G] {p α : ℕ} 
  (hp : p.prime) (ha : α > 0) (hG : card G = p ^ α) : 
  ∀ H : subgroup G, H.index = p → H.normal :=

codex statement:
theorem subgroup_of_index_prime_is_normal:
  fixes p::nat and G::"('a, 'b) monoid_scheme" (structure)
  assumes "prime p" "order G = p^a" "subgroup H G" "card (G / H) = p"
  shows "normal H G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_2_9a: undefined oops


(*
problem_number:4_2_14
natural language statement:
Let $G$ be a finite group of composite order $n$ with the property that $G$ has a subgroup of order $k$ for each positive integer $k$ dividing $n$. Prove that $G$ is not simple.
lean statement:
theorem exercise_4_2_14 {G : Type*} [fintype G] [group G] 
  (hG : ¬ (card G).prime) (hG1 : ∀ k ∣ card G, 
  ∃ (H : subgroup G) (fH : fintype H), @card H fH = k) : 
  ¬ is_simple_group G :=

codex statement:
theorem not_simple_of_composite_order_and_subgroup_of_each_divisor:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "finite_group G" "composite_group G" "∀k. k dvd order G ⟶ ∃H. subgroup H G ∧ card H = k"
  shows "¬simple_group G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_2_14: undefined oops


(*
problem_number:4_3_5
natural language statement:
If the center of $G$ is of index $n$, prove that every conjugacy class has at most $n$ elements.
lean statement:

codex statement:
theorem conjugacy_class_card_leq_index_center:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite (carrier G)" "card (center G) = n"
  shows "∀x∈carrier G. card {y∈carrier G. y = x^g ∧ g∈carrier G} ≤ n"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_3_5: undefined oops


(*
problem_number:4_3_26
natural language statement:
Let $G$ be a transitive permutation group on the finite set $A$ with $|A|>1$. Show that there is some $\sigma \in G$ such that $\sigma(a) \neq a$ for all $a \in A$.
lean statement:
theorem exercise_4_3_26 {α : Type*} [fintype α] (ha : fintype.card α > 1)
  (h_tran : ∀ a b: α, ∃ σ : equiv.perm α, σ a = b) : 
  ∃ σ : equiv.perm α, ∀ a : α, σ a ≠ a := 

codex statement:
theorem exists_permutation_of_transitive_permutation_group:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "finite (carrier G)" "transitive_on (carrier G) G" "card (carrier G) > 1"
  shows "∃ σ ∈ carrier G. ∀ a ∈ carrier G. σ a ≠ a"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_3_26: undefined oops


(*
problem_number:4_3_27
natural language statement:
Let $g_{1}, g_{2}, \ldots, g_{r}$ be representatives of the conjugacy classes of the finite group $G$ and assume these elements pairwise commute. Prove that $G$ is abelian.
lean statement:

codex statement:
theorem abelian_of_pairwise_commute:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "finite_group G" "∀i j. i ≠ j ⟶ g i ∘ g j = g j ∘ g i"
  shows "abelian_group G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_3_27: undefined oops


(*
problem_number:4_4_2
natural language statement:
Prove that if $G$ is an abelian group of order $p q$, where $p$ and $q$ are distinct primes, then $G$ is cyclic.
lean statement:
theorem exercise_4_4_2 {G : Type*} [fintype G] [group G] 
  {p q : nat.primes} (hpq : p ≠ q) (hG : card G = p*q) : 
  is_cyclic G :=

codex statement:
theorem cyclic_of_abelian_of_order_pq:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "abelian G" "order G = p * q" "prime p" "prime q" "p ≠ q"
  shows "cyclic G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4_2: undefined oops


(*
problem_number:4_4_6a
natural language statement:
Prove that characteristic subgroups are normal.
lean statement:
theorem exercise_4_4_6a {G : Type*} [group G] (H : subgroup G)
  [subgroup.characteristic H] : subgroup.normal H  :=

codex statement:
theorem characteristic_subgroup_is_normal:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "char_subgroup H G"
  shows "normal_subgroup H G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4_6a: undefined oops


(*
problem_number:4_4_6b
natural language statement:
Prove that there exists a normal subgroup that is not characteristic.
lean statement:
theorem exercise_4_4_6b {G : Type*} [group G] : 
  ∃ H : subgroup G, H.characteristic ∧ ¬ H.normal :=

codex statement:
theorem exists_normal_not_characteristic:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G"
  shows "∃H. normal_subgroup H G ∧ ¬characteristic_subgroup H G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4_6b: undefined oops


(*
problem_number:4_4_7
natural language statement:
If $H$ is the unique subgroup of a given order in a group $G$ prove $H$ is characteristic in $G$.
lean statement:
theorem exercise_4_4_7 {G : Type*} [group G] {H : subgroup G} [fintype H]
  (hH : ∀ (K : subgroup G) (fK : fintype K), card H = @card K fK → H = K) : 
  H.characteristic :=

codex statement:
theorem unique_subgroup_of_order_is_characteristic:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "group H" "order H = n" "∀H'. group H' ⟶ order H' = n ⟶ H' = H"
  shows "char_subgroup H G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4_7: undefined oops


(*
problem_number:4_4_8a
natural language statement:
Let $G$ be a group with subgroups $H$ and $K$ with $H \leq K$. Prove that if $H$ is characteristic in $K$ and $K$ is normal in $G$ then $H$ is normal in $G$.
lean statement:
theorem exercise_4_4_8a {G : Type*} [group G] (H K : subgroup G)  
  (hHK : H ≤ K) [hHK1 : (H.subgroup_of K).normal] [hK : K.normal] : 
  H.normal :=

codex statement:
theorem characteristic_subgroup_of_normal_subgroup_is_normal:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H K::"('a, 'b) submonoid" (structure)
  assumes "group G" "subgroup H G" "subgroup K G" "H ≤ K" "char_subgroup K H" "normal_subgroup K G"
  shows "normal_subgroup H G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_4_8a: undefined oops


(*
problem_number:4_5_1a
natural language statement:
Prove that if $P \in \operatorname{Syl}_{p}(G)$ and $H$ is a subgroup of $G$ containing $P$ then $P \in \operatorname{Syl}_{p}(H)$.
lean statement:
theorem exercise_4_5_1a {p : ℕ} {G : Type*} [group G] 
  {P : subgroup G} (hP : is_p_group p P) (H : subgroup G) 
  (hH : P ≤ H) : is_p_group p H :=

codex statement:
theorem sylow_subgroup_of_subgroup:
  fixes p::nat and G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "group H" "p ∣ order G" "p ∣ order H" "subgroup P G" "subgroup H G" "P ∈ sylow G p"
  shows "P ∈ sylow H p"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_1a: undefined oops


(*
problem_number:4_5_13
natural language statement:
Prove that a group of order 56 has a normal Sylow $p$-subgroup for some prime $p$ dividing its order.
lean statement:
theorem exercise_4_5_13 {G : Type*} [group G] [fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : sylow p G), P.normal :=

codex statement:
theorem exists_normal_sylow_of_order_56:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 56"
  shows "∃p. prime p ∧ p dvd order G ∧ ∃H. subgroup H G ∧ normal H G ∧ card H = p^(order G div p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_13: undefined oops


(*
problem_number:4_5_14
natural language statement:
Prove that a group of order 312 has a normal Sylow $p$-subgroup for some prime $p$ dividing its order.
lean statement:
theorem exercise_4_5_14 {G : Type*} [group G] [fintype G]
  (hG : card G = 312) :
  ∃ (p : ℕ) (P : sylow p G), P.normal :=

codex statement:
theorem exists_normal_sylow_of_order_312:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 312"
  shows "∃p. prime p ∧ p dvd order G ∧ ∃H. subgroup H G ∧ normal H G ∧ card H = p^(order G div p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_14: undefined oops


(*
problem_number:4_5_15
natural language statement:
Prove that a group of order 351 has a normal Sylow $p$-subgroup for some prime $p$ dividing its order.
lean statement:
theorem exercise_4_5_15 {G : Type*} [group G] [fintype G] 
  (hG : card G = 351) : 
  ∃ (p : ℕ) (P : sylow p G), P.normal :=

codex statement:
theorem exists_normal_sylow_of_order_351:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 351"
  shows "∃p. prime p ∧ p dvd order G ∧ ∃H. subgroup H G ∧ card H = p^(order G div p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_15: undefined oops


(*
problem_number:4_5_16
natural language statement:
Let $|G|=p q r$, where $p, q$ and $r$ are primes with $p<q<r$. Prove that $G$ has a normal Sylow subgroup for either $p, q$ or $r$.
lean statement:
theorem exercise_4_5_16 {p q r : ℕ} {G : Type*} [group G] 
  [fintype G]  (hpqr : p < q ∧ q < r) 
  (hpqr1 : p.prime ∧ q.prime ∧ r.prime)(hG : card G = p*q*r) : 
  nonempty (sylow p G) ∨ nonempty(sylow q G) ∨ nonempty(sylow r G) :=

codex statement:
theorem exists_normal_sylow_of_order_prime_prime_prime:
  fixes p q r::nat and G::"('a, 'b) monoid_scheme"
  assumes "normalization_semidom_class.prime p" "normalization_semidom_class.prime q" "normalization_semidom_class.prime r" "p < q" "q < r" "order G = p * q * r" "finite (carrier G)"
  shows "∃H. subgroup H G ∧ (∃P. sylow_subgroup G p P ∧ normal H P)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_16: undefined oops


(*
problem_number:4_5_17
natural language statement:
Prove that if $|G|=105$ then $G$ has a normal Sylow 5 -subgroup and a normal Sylow 7-subgroup.
lean statement:
theorem exercise_4_5_17 {G : Type*} [fintype G] [group G] 
  (hG : card G = 105) : 
  nonempty(sylow 5 G) ∧ nonempty(sylow 7 G) :=

codex statement:
theorem exists_normal_sylow_of_order_105:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 105"
  shows "∃H. subgroup H G ∧ normal_subgroup H G ∧ card H = 5" "∃H. subgroup H G ∧ normal_subgroup H G ∧ card H = 7"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_17: undefined oops


(*
problem_number:4_5_18
natural language statement:
Prove that a group of order 200 has a normal Sylow 5-subgroup.
lean statement:
theorem exercise_4_5_18 {G : Type*} [fintype G] [group G] 
  (hG : card G = 200) : 
  ∃ N : sylow 5 G, N.normal :=

codex statement:
theorem exists_normal_sylow_of_order_200:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 200"
  shows "∃H. subgroup H G ∧ normal H G ∧ card H = 5"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_18: undefined oops


(*
problem_number:4_5_19
natural language statement:
Prove that if $|G|=6545$ then $G$ is not simple.
lean statement:
theorem exercise_4_5_19 {G : Type*} [fintype G] [group G] 
  (hG : card G = 6545) : ¬ is_simple_group G :=

codex statement:
theorem not_simple_of_order_eq_6545:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 6545"
  shows "∃H. subgroup H G ∧ H ≠ (𝟭::'a set)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_19: undefined oops


(*
problem_number:4_5_20
natural language statement:
Prove that if $|G|=1365$ then $G$ is not simple.
lean statement:
theorem exercise_4_5_20 {G : Type*} [fintype G] [group G]
  (hG : card G = 1365) : ¬ is_simple_group G :=

codex statement:
theorem not_simple_of_order_1365:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 1365"
  shows "∃H. subgroup H G ∧ H ≠ (𝟭::'a set)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_20: undefined oops


(*
problem_number:4_5_21
natural language statement:
Prove that if $|G|=2907$ then $G$ is not simple.
lean statement:
theorem exercise_4_5_21 {G : Type*} [fintype G] [group G]
  (hG : card G = 2907) : ¬ is_simple_group G :=

codex statement:
theorem not_simple_of_order_2907:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 2907"
  shows "∃H. subgroup H G ∧ H ≠ {𝟭} ∧ H ≠ carrier G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_21: undefined oops


(*
problem_number:4_5_22
natural language statement:
Prove that if $|G|=132$ then $G$ is not simple.
lean statement:
theorem exercise_4_5_22 {G : Type*} [fintype G] [group G]
  (hG : card G = 132) : ¬ is_simple_group G :=

codex statement:
theorem not_simple_of_order_eq_132:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 132"
  shows "∃H. subgroup H G ∧ H ≠ (𝟭::'a set)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_22: undefined oops


(*
problem_number:4_5_23
natural language statement:
Prove that if $|G|=462$ then $G$ is not simple.
lean statement:
theorem exercise_4_5_23 {G : Type*} [fintype G] [group G]
  (hG : card G = 462) : ¬ is_simple_group G :=

codex statement:
theorem not_simple_of_order_462:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 462"
  shows "∃H. subgroup H G ∧ H ≠ (𝟭::'a set)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_23: undefined oops


(*
problem_number:4_5_28
natural language statement:
Let $G$ be a group of order 105. Prove that if a Sylow 3-subgroup of $G$ is normal then $G$ is abelian.
lean statement:
theorem exercise_4_5_28 {G : Type*} [group G] [fintype G] 
  (hG : card G = 105) (P : sylow 3 G) [hP : P.normal] : 
  comm_group G :=

codex statement:
theorem abelian_of_sylow_3_normal:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "order G = 105" "∃H. subgroup H G ∧ card H = 9 ∧ normal_subgroup H G"
  shows "abelian G"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_28: undefined oops


(*
problem_number:4_5_33
natural language statement:
Let $P$ be a normal Sylow $p$-subgroup of $G$ and let $H$ be any subgroup of $G$. Prove that $P \cap H$ is the unique Sylow $p$-subgroup of $H$.
lean statement:
theorem exercise_4_5_33 {G : Type*} [group G] [fintype G] {p : ℕ} 
  (P : sylow p G) [hP : P.normal] (H : subgroup G) [fintype H] : 
  ∀ R : sylow p H, R.to_subgroup = (H ⊓ P.to_subgroup).subgroup_of H ∧
  nonempty (sylow p H) :=

codex statement:
theorem unique_sylow_of_normal_sylow_intersect_subgroup:
  fixes p::nat and G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "normalization_semidom_class.prime p" "group G" "group H" "Sylow p G P" "P ⊆ H"
  shows "Sylow p H (P ∩ H)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_4_5_33: undefined oops


(*
problem_number:5_4_2
natural language statement:
Prove that a subgroup $H$ of $G$ is normal if and only if $[G, H] \leq H$.
lean statement:
theorem exercise_5_4_2 {G : Type*} [group G] (H : subgroup G) : 
  H.normal ↔ ⁅(⊤ : subgroup G), H⁆ ≤ H := 

codex statement:
theorem normal_iff_commutator_subset:
  fixes G::"('a, 'b) monoid_scheme" (structure) and H::"('a, 'b) monoid_scheme" (structure)
  assumes "group G" "subgroup H G"
  shows "normal H G ⟷ commutator G H ≤ H"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_5_4_2: undefined oops


(*
problem_number:7_1_2
natural language statement:
Prove that if $u$ is a unit in $R$ then so is $-u$.
lean statement:
theorem exercise_7_1_2 {R : Type*} [ring R] {u : R}
  (hu : is_unit u) : is_unit (-u) :=

codex statement:
theorem unit_of_unit_neg:
  fixes R::"'a::ring_1"
  assumes "unit R u"
  shows "unit R (-u)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_1_2: undefined oops


(*
problem_number:7_1_11
natural language statement:
Prove that if $R$ is an integral domain and $x^{2}=1$ for some $x \in R$ then $x=\pm 1$.
lean statement:
theorem exercise_7_1_11 {R : Type*} [ring R] [is_domain R] 
  {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1 :=

codex statement:
theorem eq_one_or_minus_one_of_square_eq_one:
  fixes R::"'a::idom ring"
  assumes "x^2 = 1"
  shows "x = 1 ∨ x = -1"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_1_11: undefined oops


(*
problem_number:7_1_12
natural language statement:
Prove that any subring of a field which contains the identity is an integral domain.
lean statement:
theorem exercise_7_1_12 {F : Type*} [field F] {K : subring F}
  (hK : (1 : F) ∈ K) : is_domain K :=

codex statement:
theorem subring_of_field_is_integral_domain:
  fixes R::"'a::field ring"
  assumes "subring R" "1∈carrier R"
  shows "integral_domain R"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_1_12: undefined oops


(*
problem_number:7_1_15
natural language statement:
A ring $R$ is called a Boolean ring if $a^{2}=a$ for all $a \in R$. Prove that every Boolean ring is commutative.
lean statement:
theorem exercise_7_1_15 {R : Type*} [ring R] (hR : ∀ a : R, a^2 = a) :
  comm_ring R :=

codex statement:
theorem boolean_ring_is_commutative:
  fixes R::"'a::comm_ring_1 ring"
  assumes "∀a. a^2 = a"
  shows "comm_ring R"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_1_15: undefined oops


(*
problem_number:7_2_2
natural language statement:
Let $p(x)=a_{n} x^{n}+a_{n-1} x^{n-1}+\cdots+a_{1} x+a_{0}$ be an element of the polynomial ring $R[x]$. Prove that $p(x)$ is a zero divisor in $R[x]$ if and only if there is a nonzero $b \in R$ such that $b p(x)=0$.
lean statement:
theorem exercise_7_2_2 {R : Type*} [ring R] (p : polynomial R) :
  p ∣ 0 ↔ ∃ b : R, b ≠ 0 ∧ b • p = 0 := 

codex statement:
theorem zero_divisor_of_polynomial_iff_exists_nonzero_mult_zero:
  fixes R::"'a::comm_ring_1 ring" and p::"'a poly"
  assumes "p ≠ 0"
  shows "∃b. b ≠ 0 ∧ b * p = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_2_2: undefined oops


(*
problem_number:7_2_4
natural language statement:
Prove that if $R$ is an integral domain then the ring of formal power series $R[[x]]$ is also an integral domain.
lean statement:

codex statement:
theorem integral_domain_of_formal_power_series:
  fixes R::"'a::comm_ring_1 ring"
  assumes "integral_domain R"
  shows "integral_domain (R⟶₀)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_2_4: undefined oops


(*
problem_number:7_2_12
natural language statement:
Let $G=\left\{g_{1}, \ldots, g_{n}\right\}$ be a finite group. Prove that the element $N=g_{1}+g_{2}+\ldots+g_{n}$ is in the center of the group ring $R G$.
lean statement:
theorem exercise_7_2_12 {R G : Type*} [ring R] [group G] [fintype G] : 
  ∑ g : G, monoid_algebra.of R G g ∈ center (monoid_algebra R G) :=

codex statement:
theorem sum_of_elements_in_center_of_group_ring:
  fixes G::"('a, 'b) monoid_scheme" (structure)
  assumes "finite (carrier G)"
  shows "∀x∈carrier G. (∑y∈carrier G. y) * x = x * (∑y∈carrier G. y)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_2_12: undefined oops


(*
problem_number:7_3_16
natural language statement:
Let $\varphi: R \rightarrow S$ be a surjective homomorphism of rings. Prove that the image of the center of $R$ is contained in the center of $S$.
lean statement:
theorem exercise_7_3_16 {R S : Type*} [ring R] [ring S] 
  {φ : R →+* S} (hf : surjective φ) : 
  φ '' (center R) ⊂ center S :=

codex statement:
theorem center_of_ring_hom_image_subset_center_of_ring_hom_codomain:
  fixes R S::"'a::comm_ring_1 ring" and φ::"'a ⇒ 'b::comm_ring_1"
  assumes "ring R" "ring S" "ring_hom φ R S" "surj φ"
  shows "φ ` center R ⊆ center S"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_3_16: undefined oops


(*
problem_number:7_3_28
natural language statement:
Prove that an integral domain has characteristic $p$, where $p$ is either a prime or 0.
lean statement:

codex statement:
theorem char_of_integral_domain:
  fixes R::"'a::{comm_ring_1,ring_no_zero_divisors}"
  assumes "integral_domain R"
  shows "char R = 0 ∨ char R = prime (char R)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_3_28: undefined oops


(*
problem_number:7_3_37
natural language statement:
An ideal $N$ is called nilpotent if $N^{n}$ is the zero ideal for some $n \geq 1$. Prove that the ideal $p \mathbb{Z} / p^{m} \mathbb{Z}$ is a nilpotent ideal in the ring $\mathbb{Z} / p^{m} \mathbb{Z}$.
lean statement:
theorem exercise_7_3_37 {R : Type*} {p m : ℕ} (hp : p.prime) 
  (N : ideal $ zmod $ p^m) : 
  is_nilpotent N ↔  is_nilpotent (ideal.span ({p} : set $ zmod $ p^m)) :=

codex statement:
theorem nilpotent_ideal_of_p_Z_mod_p_m_Z:
  fixes p::nat and m::nat
  assumes "prime p"
  shows "∃n. (p^n) *⇩R (p^m) = 0"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_3_37: undefined oops


(*
problem_number:7_4_27
natural language statement:
Let $R$ be a commutative ring with $1 \neq 0$. Prove that if $a$ is a nilpotent element of $R$ then $1-a b$ is a unit for all $b \in R$.
lean statement:
theorem exercise_7_4_27 {R : Type*} [comm_ring R] (hR : (0 : R) ≠ 1) 
  {a : R} (ha : is_nilpotent a) (b : R) : 
  is_unit (1-a*b) :=

codex statement:
theorem unit_of_nilpotent_of_commutative_ring:
  fixes R::"'a::comm_ring_1"
  assumes "a∈carrier R" "a [^] n = 0"
  shows "∀b∈carrier R. (1 - a * b) ∈ Units R"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_7_4_27: undefined oops


(*
problem_number:8_1_12
natural language statement:
Let $N$ be a positive integer. Let $M$ be an integer relatively prime to $N$ and let $d$ be an integer relatively prime to $\varphi(N)$, where $\varphi$ denotes Euler's $\varphi$-function. Prove that if $M_{1} \equiv M^{d} \pmod N$ then $M \equiv M_{1}^{d^{\prime}} \pmod N$ where $d^{\prime}$ is the inverse of $d \bmod \varphi(N)$: $d d^{\prime} \equiv 1 \pmod {\varphi(N)}$.
lean statement:
theorem exercise_8_1_12 {N : ℕ} (hN : N > 0) {M M': ℤ} {d : ℕ}
  (hMN : M.gcd N = 1) (hMd : d.gcd N.totient = 1) 
  (hM' : M' ≡ M^d [ZMOD N]) : 
  ∃ d' : ℕ, d' * d ≡ 1 [ZMOD N.totient] ∧ 
  M ≡ M'^d' [ZMOD N] :=

codex statement:
theorem congruent_mod_of_congruent_mod_power_of_inverse_mod_phi:
  fixes N::nat and M::int and M1::int and d::int
  assumes "prime N" "coprime M N" "coprime d (φ N)" "M1 ≡ M^d [MOD N]"
  shows "M ≡ M1^(inverse_mod (φ N) d) [MOD N]"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_8_1_12: undefined oops


(*
problem_number:8_2_4
natural language statement:
Let $R$ be an integral domain. Prove that if the following two conditions hold then $R$ is a Principal Ideal Domain: (i) any two nonzero elements $a$ and $b$ in $R$ have a greatest common divisor which can be written in the form $r a+s b$ for some $r, s \in R$, and (ii) if $a_{1}, a_{2}, a_{3}, \ldots$ are nonzero elements of $R$ such that $a_{i+1} \mid a_{i}$ for all $i$, then there is a positive integer $N$ such that $a_{n}$ is a unit times $a_{N}$ for all $n \geq N$.
lean statement:
theorem exercise_8_2_4 {R : Type*} [ring R][no_zero_divisors R] 
  [cancel_comm_monoid_with_zero R] [gcd_monoid R]
  (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r*a + s*b)
  (h2 : ∀ a : ℕ → R, (∀ i j : ℕ, i < j → a i ∣ a j) → 
  ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, is_unit u ∧ a n = u * a N) : 
  is_principal_ideal_ring R :=

codex statement:
theorem PID_of_gcd_and_divides_of_nonzero_elements:
  fixes R::"'a::idom ring"
  assumes "∀a b. a ≠ 0 ∧ b ≠ 0 ⟶ ∃r s. gcd a b = r * a + s * b" "∀a b. a ≠ 0 ∧ b ≠ 0 ⟶ ∃N. ∀n≥N. a dvd b ^ n"
  shows "principal_ideal_ring R"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_8_2_4: undefined oops


(*
problem_number:8_3_4
natural language statement:
Prove that if an integer is the sum of two rational squares, then it is the sum of two integer squares.
lean statement:
theorem exercise_8_3_4 {R : Type*} {n : ℤ} {r s : ℚ} 
  (h : r^2 + s^2 = n) : 
  ∃ a b : ℤ, a^2 + b^2 = n :=

codex statement:
theorem sum_of_two_rational_squares_is_sum_of_two_integer_squares:
  fixes a b::int
  assumes "∃x y. x∈ℚ ∧ y∈ℚ ∧ a = x^2 + y^2"
  shows "∃x y. x∈ℤ ∧ y∈ℤ ∧ a = x^2 + y^2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_8_3_4: undefined oops


(*
problem_number:8_3_5a
natural language statement:
Let $R=\mathbb{Z}[\sqrt{-n}]$ where $n$ is a squarefree integer greater than 3. Prove that $2, \sqrt{-n}$ and $1+\sqrt{-n}$ are irreducibles in $R$.
lean statement:
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : squarefree n) : 
  irreducible (2 :zsqrtd $ -n) ∧ 
  irreducible (⟨0, 1⟩ : zsqrtd $ -n) ∧ 
  irreducible (1 + ⟨0, 1⟩ : zsqrtd $ -n) :=

codex statement:
theorem irreducible_of_squarefree_int_greater_3:
  fixes n::int
  assumes "n > 3" "∀p. prime p ⟶ p ∣ n ⟶ p dvd 1 ∨ p dvd 2"
  shows "∀x. x ∈ {2, √ (-n), 1 + √ (-n)} ⟶ irreducible x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_8_3_5a: undefined oops


(*
problem_number:8_3_6a
natural language statement:
Prove that the quotient ring $\mathbb{Z}[i] /(1+i)$ is a field of order 2.
lean statement:
theorem exercise_8_3_6a {R : Type*} [ring R]
  (hR : R = (gaussian_int ⧸ ideal.span ({⟨0, 1⟩} : set gaussian_int))) :
  is_field R ∧ ∃ finR : fintype R, @card R finR = 2 :=

codex statement:
theorem quotient_ring_is_field_of_order_2:
  assumes "ideal (1 + I) (ℤ[I])"
  shows "field (ℤ[I] /⟦1 + I⟧)" "card (carrier (ℤ[I] /⟦1 + I⟧)) = 2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_8_3_6a: undefined oops


(*
problem_number:8_3_6b
natural language statement:
Let $q \in \mathbb{Z}$ be a prime with $q \equiv 3 \bmod 4$. Prove that the quotient ring $\mathbb{Z}[i] /(q)$ is a field with $q^{2}$ elements.
lean statement:
theorem exercise_8_3_6b {q : ℕ} (hq0 : q.prime) 
  (hq1 : q ≡ 3 [ZMOD 4]) {R : Type*} [ring R]
  (hR : R = (gaussian_int ⧸ ideal.span ({q} : set gaussian_int))) : 
  is_field R ∧ ∃ finR : fintype R, @card R finR = q^2 :=

codex statement:
theorem quotient_ring_is_field:
  fixes q::int
  assumes "prime q" "q ≡ 3 [MOD 4]"
  shows "field (quotient_ring (ℤ[i]) (ideal_generated ℤ {q}))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_8_3_6b: undefined oops


(*
problem_number:9_1_6
natural language statement:
Prove that $(x, y)$ is not a principal ideal in $\mathbb{Q}[x, y]$.
lean statement:
theorem exercise_9_1_6 : ¬ is_principal 
  (ideal.span ({X 0, X 1} : set (mv_polynomial (fin 2) ℚ))) :=

codex statement:

Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_1_6: undefined oops


(*
problem_number:9_1_10
natural language statement:
Prove that the ring $\mathbb{Z}\left[x_{1}, x_{2}, x_{3}, \ldots\right] /\left(x_{1} x_{2}, x_{3} x_{4}, x_{5} x_{6}, \ldots\right)$ contains infinitely many minimal prime ideals (cf. exercise.9.1.36 of Section 7.4).
lean statement:
theorem exercise_9_1_10 {f : ℕ → mv_polynomial ℕ ℤ} 
  (hf : f = λ i, X i * X (i+1)): 
  infinite (minimal_primes (mv_polynomial ℕ ℤ ⧸ ideal.span (range f))) := 

codex statement:
theorem infinite_minimal_prime_ideals_of_quotient_ring:
  fixes R::"('a::comm_ring_1) ring"
  assumes "∀i. prime (p i)" "∀i. ideal R (p i)" "∀i. p (2*i) ∩ p (2*i+1) = {0}"
  shows "infinite {P. prime_ideal R P ∧ ∀Q. prime_ideal R Q ⟶ Q ≤ P ⟹ Q = P}"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_1_10: undefined oops


(*
problem_number:9_3_2
natural language statement:
Prove that if $f(x)$ and $g(x)$ are polynomials with rational coefficients whose product $f(x) g(x)$ has integer coefficients, then the product of any coefficient of $g(x)$ with any coefficient of $f(x)$ is an integer.
lean statement:
theorem exercise_9_3_2 {f g : polynomial ℚ} (i j : ℕ)
  (hfg : ∀ n : ℕ, ∃ a : ℤ, (f*g).coeff = a) :
  ∃ a : ℤ, f.coeff i * g.coeff j = a :=

codex statement:
theorem product_of_coeff_of_poly_with_rational_coeff_is_integer:
  fixes f g::"real ⇒ real"
  assumes "polynomial f" "polynomial g" "∀x. (f x * g x) ∈ ℤ"
  shows "∀x. (coeff f x * coeff g x) ∈ ℤ"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_3_2: undefined oops


(*
problem_number:9_4_2a
natural language statement:
Prove that $x^4-4x^3+6$ is irreducible in $\mathbb{Z}[x]$.
lean statement:
theorem exercise_9_4_2a : irreducible (X^4 - 4*X^3 + 6 : polynomial ℤ) := 

codex statement:
theorem irreducible_of_polynomial_of_degree_4:
  fixes x::"int poly"
  assumes "degree x = 4" "coeff x 0 = 6" "coeff x 1 = 0" "coeff x 2 = -4" "coeff x 3 = 0" "coeff x 4 = 1"
  shows "irreducible x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_4_2a: undefined oops


(*
problem_number:9_4_2b
natural language statement:
Prove that $x^6+30x^5-15x^+6x-120$ is irreducible in $\mathbb{Z}[x]$.
lean statement:
theorem exercise_9_4_2b : irreducible 
  (X^6 + 30*X^5 - 15*X^3 + 6*X - 120 : polynomial ℤ) :=

codex statement:
theorem irreducible_polynomial:
  fixes x::"int poly"
  assumes "degree x = 6" "∀y. degree y = 5 ⟶ y dvd x ⟶ y = [:1:]"
  shows "irreducible x"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_4_2b: undefined oops


(*
problem_number:9_4_2c
natural language statement:
Prove that $x^4+4x^3+6x^2+2x+1$ is irreducible in $\mathbb{Z}[x]$.
lean statement:
theorem exercise_9_4_2c : irreducible 
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : polynomial ℤ) :=

codex statement:
theorem irreducible_polynomial_of_degree_4:
  fixes x::"int poly"
  shows "irreducible (x^4 + 4*x^3 + 6*x^2 + 2*x + 1)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_4_2c: undefined oops


(*
problem_number:9_4_2d
natural language statement:
Prove that $\frac{(x+2)^p-2^p}{x}$, where $p$ is an odd prime, is irreducible in $\mathbb{Z}[x]$.
lean statement:
theorem exercise_9_4_2d {p : ℕ} (hp : p.prime ∧ p > 2) 
  {f : polynomial ℤ} (hf : f = (X + 2)^p): 
  irreducible (∑ n in (f.support - {0}), (f.coeff n) * X ^ (n-1) : 
  polynomial ℤ) :=

codex statement:
theorem irreducible_of_odd_prime:
  fixes p::nat
  assumes "prime p" "odd p"
  shows "irreducible (poly_of_nat p * (X + 2) - 2^p)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_4_2d: undefined oops


(*
problem_number:9_4_9
natural language statement:
Prove that the polynomial $x^{2}-\sqrt{2}$ is irreducible over $\mathbb{Z}[\sqrt{2}]$. You may assume that $\mathbb{Z}[\sqrt{2}]$ is a U.F.D.
lean statement:
theorem exercise_9_4_9 : 
  irreducible (X^2 - C sqrtd : polynomial (zsqrtd 2)) :=

codex statement:
theorem irreducible_of_polynomial_of_sqrt_two:
  fixes x::"'a::{idom,ring_char_0}"
  assumes "char_poly (x, 1) = [:1, 0, -sqrt 2:]"
  shows "irreducible (char_poly (x, 1))"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_4_9: undefined oops


(*
problem_number:9_4_11
natural language statement:
Prove that $x^2+y^2-1$ is irreducible in $\mathbb{Q}[x,y]$.
lean statement:
theorem exercise_9_4_11 : 
  irreducible ((X 0)^2 + (X 1)^2 - 1 : mv_polynomial (fin 2) ℚ) :=

codex statement:
theorem irreducible_of_polynomial_ring:
  fixes x y::"'a::{idom,ring_char_0}"
  shows "irreducible (x^2 + y^2 - 1)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_9_4_11: undefined oops


(*
problem_number:11_1_13
natural language statement:
Prove that as vector spaces over $\mathbb{Q}, \mathbb{R}^n \cong \mathbb{R}$, for all $n \in \mathbb{Z}^{+}$.
lean statement:
theorem exercise_11_1_13 {ι : Type*} [fintype ι] : 
  (ι → ℝ) ≃ₗ[ℚ] ℝ :=

codex statement:
theorem isomorphic_of_vector_space_over_Q:
  fixes n::nat
  shows "vector_space ℚ (UNIV::'a::euclidean_space set)" "vector_space ℚ (UNIV::'b::euclidean_space set)" "n = DIM('a)" "n = DIM('b)"
  shows "('a::euclidean_space) ≃ₗ[ℚ] ('b::euclidean_space)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_11_1_13: undefined oops


(*
problem_number:11_3_3bi
natural language statement:
Let $S$ be any subset of $V^*$ for some finite dimensional space $V$. Define $\operatorname{Ann}(S)=\{v \in V \mid f(v)=0 \text{ for all } f \in S\}$. Let $W_1$ and $W_2$ be subspaces of $V^*$. Prove that $\operatorname{Ann}(W_1+W_2)=\operatorname{Ann}(W_1) \cap\operatorname{Ann}(W_2)$.
lean statement:

codex statement:
theorem Ann_sum_eq_inter_Ann:
  fixes V::"'a::euclidean_space set" and W1 W2::"'a set"
  assumes "subspace W1" "subspace W2"
  shows "Ann (W1 + W2) = Ann W1 ∩ Ann W2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_11_3_3bi: undefined oops


(*
problem_number:11_3_3bii
natural language statement:
Let $S$ be any subset of $V^*$ for some finite dimensional space $V$. Define $\operatorname{Ann}(S)=\{v \in V \mid f(v)=0 \text{ for all } f \in S\}$. Let $W_1$ and $W_2$ be subspaces of $V^*$. Prove that $\operatorname{Ann}(W_1\cap W_2)=\operatorname{Ann}(W_1) + \operatorname{Ann}(W_2)$.
lean statement:

codex statement:
theorem Ann_inter_eq_Ann_sum:
  fixes V::"'a::euclidean_space set" and W1 W2::"'a set"
  assumes "subspace W1" "subspace W2"
  shows "Ann (W1 ∩ W2) = Ann W1 + Ann W2"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_11_3_3bii: undefined oops


(*
problem_number:11_3_3c
natural language statement:
Let $S$ be any subset of $V^*$ for some finite dimensional space $V$. Define $\operatorname{Ann}(S)=\{v \in V \mid f(v)=0 \text{ for all } f \in S\}$. Let $W_1$ and $W_2$ be subspaces of $V^*$. Prove that $W_1=W_2$ if and only if $\operatorname{Ann}(W_1)=\operatorname{Ann}(W_2)$.
lean statement:

codex statement:
theorem Ann_eq_iff_eq:
  fixes V::"'a::euclidean_space set" and W1 W2::"'a set"
  assumes "subspace W1" "subspace W2"
  shows "W1 = W2 ⟷ (Ann W1 = Ann W2)"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_11_3_3c: undefined oops


(*
problem_number:11_3f
natural language statement:
Let $S$ be any subset of $V^*$ for some finite dimensional space $V$. Define $\operatorname{Ann}(S)=\{v \in V \mid f(v)=0 \text{ for all } f \in S\}$. Let $W_1$ and $W_2$ be subspaces of $V^*$. Prove that if $W^*$ is any subspace of $V^*$ then $\operatorname{dim} \operatorname{Ann}(W^* )=\operatorname{dim} V-\operatorname{dim} W^*$.
lean statement:

codex statement:
theorem dim_ann_eq_dim_v_sub_dim_w:
  fixes V::"'a::euclidean_space set" and W::"'a set"
  assumes "finite_dimensional V" "subspace W"
  shows "dim (ann W) = dim V - dim W"
Our comment on the codex statement: <YOU CAN LEAVE YOUR COMMENT HERE>
 *)
theorem exercise_11_3f: undefined oops




end