
Theory func1
theory func1
imports Fol1 ZF1
```mathlab
(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2005 - 2019  Slawomir Kolodynski

    This program is free software Redistribution and use in source and binary forms, 
    with or without modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, 
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice, 
   this list of conditions and the following disclaimer in the documentation and/or 
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products 
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED 
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF 
MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, 
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS 
OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR 
OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, 
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section ‹Functions - introduction›

theory func1 imports ZF.func Fol1 ZF1

begin

text‹This theory covers basic properties of function spaces.
  A set of functions with domain $X$ and values in the set $Y$
  is denoted in Isabelle as $X\rightarrow Y$. It just happens
  that the colon ":" is a synonym of the set membership symbol
  $\in$ in Isabelle/ZF so we can write $f:X\rightarrow Y$ instead of 
  $f \in X\rightarrow Y$. This is the only case that we use the colon 
  instead of the regular set membership symbol.›

subsection‹Properties of functions, function spaces and (inverse) images.›

text‹Functions in ZF are sets of pairs. This means
  that if $f: X\rightarrow Y $ then $f\subseteq X\times Y$.
  This section is mostly about consequences of this understanding 
  of the notion of function.
›

text‹We define the notion of function that preserves a collection here.
  Given two collection of sets a function preserves the collections if 
  the inverse image of sets in one collection belongs to the second one.
  This notion does not have a name in romantic math. It is used to define 
  continuous functions in ‹Topology_ZF_2› theory. 
  We define it here so that we can 
  use it for other purposes, like defining measurable functions.
  Recall that ‹f-``(A)› means the inverse image of the set $A$.›

definition
  "PresColl(f,S,T) ≡ ∀ A∈T. f-``(A)∈S"

text‹A definition that allows to get the first factor of the
  domain of a binary function $f: X\times Y \rightarrow Z$.›

definition
  "fstdom(f) ≡ domain(domain(f))"

text‹If a function maps $A$ into another set, then $A$ is the 
  domain of the function.›

lemma func1_1_L1: assumes "f:A→C" shows "domain(f) = A"
  using assms domain_of_fun by simp

text‹Standard Isabelle defines a ‹function(f)› predicate.
  The next lemma shows that our functions satisfy that predicate. 
  It is a special version of Isabelle's ‹fun_is_function›.›

lemma fun_is_fun: assumes "f:X→Y" shows "function(f)"
  using assms fun_is_function by simp

text‹A lemma explains what ‹fstdom› is for.›

lemma fstdomdef: assumes A1: "f: X×Y → Z" and A2: "Y≠0" 
  shows "fstdom(f) = X"
proof -
  from A1 have "domain(f) = X×Y" using func1_1_L1
    by simp
  with A2 show "fstdom(f) = X" unfolding fstdom_def by auto
qed

text‹A version of the ‹Pi_type› lemma from the standard Isabelle/ZF library.›

lemma func1_1_L1A: assumes A1: "f:X→Y" and A2: "∀x∈X. f`(x) ∈ Z"
  shows "f:X→Z"
proof -
  { fix x assume "x∈X" 
    with A2 have "f`(x) ∈ Z" by simp }
  with A1 show "f:X→Z" by (rule Pi_type)
qed

text‹A variant of ‹func1_1_L1A›.›

lemma func1_1_L1B: assumes A1: "f:X→Y" and A2: "Y⊆Z"
  shows "f:X→Z"
proof -
  from A1 A2 have "∀x∈X. f`(x) ∈ Z"
    using apply_funtype by auto
  with A1 show  "f:X→Z" using func1_1_L1A by blast
qed

text‹There is a value for each argument.›

lemma func1_1_L2: assumes A1: "f:X→Y"  "x∈X" 
  shows "∃y∈Y. ⟨x,y⟩ ∈ f"  
proof-
  from A1 have "f`(x) ∈ Y" using apply_type by simp
  moreover from A1 have "⟨ x,f`(x)⟩∈ f" using apply_Pair by simp
  ultimately show ?thesis by auto
qed

text‹The inverse image is the image of converse. True for relations as well.›

lemma vimage_converse: shows "r-``(A) = converse(r)``(A)"
  using vimage_iff image_iff converse_iff by auto

text‹The image is the inverse image of converse.›

lemma image_converse: shows "converse(r)-``(A) = r``(A)"
  using vimage_iff image_iff converse_iff by auto

text‹The inverse image by a composition is the composition of inverse images.›

lemma vimage_comp: shows "(r O s)-``(A) = s-``(r-``(A))"
  using vimage_converse converse_comp image_comp image_converse by simp 

text‹A version of ‹vimage_comp› for three functions.›

lemma vimage_comp3: shows "(r O s O t)-``(A) = t-``(s-``(r-``(A)))"
  using vimage_comp by simp

text‹Inverse image of any set is contained in the domain.›

lemma func1_1_L3: assumes A1: "f:X→Y" shows "f-``(D) ⊆ X"
proof-
   have "∀x. x∈f-``(D) ⟶ x ∈ domain(f)"
      using  vimage_iff domain_iff by auto
    with A1 have "∀x. (x ∈ f-``(D)) ⟶ (x∈X)" using func1_1_L1 by simp
    then show ?thesis by auto
qed

text‹The inverse image of the range is the domain.›

lemma func1_1_L4: assumes "f:X→Y" shows "f-``(Y) = X"
  using assms func1_1_L3 func1_1_L2 vimage_iff by blast

text‹The arguments belongs to the domain and values to the range.›

lemma func1_1_L5: 
  assumes A1: "⟨ x,y⟩ ∈ f" and A2: "f:X→Y"  
  shows "x∈X ∧ y∈Y" 
proof
  from A1 A2 show "x∈X" using apply_iff by simp
  with A2 have "f`(x)∈ Y" using apply_type by simp
  with A1 A2 show "y∈Y" using apply_iff by simp
qed

text‹Function is a subset of cartesian product.›

lemma fun_subset_prod: assumes A1: "f:X→Y" shows "f ⊆ X×Y"
proof
  fix p assume "p ∈ f"
  with A1 have "∃x∈X. p = ⟨x, f`(x)⟩"
    using Pi_memberD by simp
  then obtain x where I: "p = ⟨x, f`(x)⟩"
    by auto
  with A1 ‹p ∈ f› have "x∈X ∧ f`(x) ∈ Y"
    using func1_1_L5 by blast
  with I show "p ∈ X×Y" by auto
qed
  
text‹The (argument, value) pair belongs to the graph of the function.›

lemma func1_1_L5A: 
  assumes A1: "f:X→Y"  "x∈X"  "y = f`(x)"
  shows "⟨x,y⟩ ∈ f"  "y ∈ range(f)" 
proof -
  from A1 show "⟨x,y⟩ ∈ f" using apply_Pair by simp
  then show "y ∈ range(f)" using rangeI by simp
qed

text‹The next theorem illustrates the meaning of the concept of 
  function in ZF.›

theorem fun_is_set_of_pairs: assumes A1: "f:X→Y"
  shows "f = {⟨x, f`(x)⟩. x ∈ X}"
proof
  from A1 show "{⟨x, f`(x)⟩. x ∈ X} ⊆ f" using func1_1_L5A
    by auto
next
  { fix p assume "p ∈ f"
    with A1 have "p ∈ X×Y" using fun_subset_prod
      by auto
    with A1 ‹p ∈ f› have "p ∈ {⟨x, f`(x)⟩. x ∈ X}" 
      using apply_equality by auto
  } thus "f ⊆ {⟨x, f`(x)⟩. x ∈ X}" by auto
qed

text‹The range of function that maps $X$ into $Y$ is contained in $Y$.›

lemma func1_1_L5B: 
  assumes  A1: "f:X→Y" shows "range(f) ⊆ Y"
proof
  fix y assume "y ∈ range(f)"
  then obtain x where "⟨ x,y⟩ ∈ f"
    using range_def converse_def domain_def by auto
  with A1 show "y∈Y" using func1_1_L5 by blast
qed

text‹The image of any set is contained in the range.›

lemma func1_1_L6: assumes A1: "f:X→Y" 
  shows "f``(B) ⊆ range(f)" and "f``(B) ⊆ Y"
proof -
  show "f``(B) ⊆ range(f)" using image_iff rangeI by auto
  with A1 show "f``(B) ⊆ Y" using func1_1_L5B by blast
qed  

text‹The inverse image of any set is contained in the domain.›

lemma func1_1_L6A: assumes A1: "f:X→Y" shows "f-``(A)⊆X"
proof
  fix x
  assume A2: "x∈f-``(A)" then obtain y where "⟨ x,y⟩ ∈ f" 
    using vimage_iff by auto
  with A1 show  "x∈X" using func1_1_L5 by fast
qed

text‹Image of a greater set is greater.›

lemma func1_1_L8: assumes A1: "A⊆B"  shows "f``(A)⊆ f``(B)"
  using assms image_Un by auto

text‹A set is contained in the the inverse image of its image.
  There is similar theorem in ‹equalities.thy›
  (‹function_image_vimage›)
  which shows that the image of inverse image of a set 
  is contained in the set.›

lemma func1_1_L9: assumes A1: "f:X→Y" and A2: "A⊆X"
  shows "A ⊆ f-``(f``(A))"
proof -
  from A1 A2 have "∀x∈A. ⟨ x,f`(x)⟩ ∈ f"  using apply_Pair by auto
  then show ?thesis using image_iff by auto
qed

text‹The inverse image of the image of the domain is the domain.›

lemma inv_im_dom: assumes A1: "f:X→Y" shows "f-``(f``(X)) = X"
proof
  from A1 show "f-``(f``(X)) ⊆ X" using func1_1_L3 by simp
  from A1 show "X ⊆ f-``(f``(X))" using func1_1_L9 by simp
qed

text‹A technical lemma needed to make the ‹func1_1_L11› 
  proof more clear.›

lemma func1_1_L10: 
  assumes A1: "f ⊆ X×Y" and A2: "∃!y. (y∈Y ∧ ⟨x,y⟩ ∈ f)"
  shows "∃!y. ⟨x,y⟩ ∈ f"
proof
  from A2 show "∃y. ⟨x, y⟩ ∈ f" by auto
  fix y n assume "⟨x,y⟩ ∈ f" and "⟨x,n⟩ ∈ f"
  with A1 A2 show "y=n" by auto
qed

text‹If $f\subseteq X\times Y$ and for every $x\in X$ there is exactly 
one $y\in Y$ such that $(x,y)\in f$ then $f$ maps $X$ to $Y$.›

lemma func1_1_L11: 
  assumes "f ⊆ X×Y" and "∀x∈X. ∃!y. y∈Y ∧ ⟨x,y⟩ ∈ f"
  shows "f: X→Y" using assms func1_1_L10 Pi_iff_old by simp

text‹A set defined by a lambda-type expression is a fuction. There is a 
  similar lemma in func.thy, but I had problems with lambda expressions syntax
  so I could not apply it. This lemma is a workaround for this. Besides, lambda
  expressions are not readable.
›

lemma func1_1_L11A: assumes A1: "∀x∈X. b(x) ∈ Y"
  shows "{⟨ x,y⟩ ∈ X×Y. b(x) = y} : X→Y"
proof -
  let ?f = "{⟨ x,y⟩ ∈ X×Y. b(x) = y}"
  have "?f ⊆ X×Y" by auto
  moreover have "∀x∈X. ∃!y. y∈Y ∧ ⟨ x,y⟩ ∈ ?f"
  proof
    fix x assume A2: "x∈X"
    show "∃!y. y∈Y ∧ ⟨x, y⟩ ∈ {⟨x,y⟩ ∈ X×Y . b(x) = y}"
    proof
      from A2 A1 show 
        "∃y. y∈Y ∧ ⟨x, y⟩ ∈ {⟨x,y⟩ ∈ X×Y . b(x) = y}"
	by simp
    next
      fix y y1
      assume "y∈Y ∧ ⟨x, y⟩ ∈ {⟨x,y⟩ ∈ X×Y . b(x) = y}"
	and "y1∈Y ∧ ⟨x, y1⟩ ∈ {⟨x,y⟩ ∈ X×Y . b(x) = y}"
      then show "y = y1" by simp
    qed
  qed
  ultimately show "{⟨ x,y⟩ ∈ X×Y. b(x) = y} : X→Y" 
    using func1_1_L11 by simp
qed

text‹The next lemma will replace ‹func1_1_L11A› one day.›

lemma ZF_fun_from_total: assumes A1: "∀x∈X. b(x) ∈ Y"
  shows "{⟨x,b(x)⟩. x∈X} : X→Y"
proof -
  let ?f = "{⟨x,b(x)⟩. x∈X}"
  { fix x assume A2: "x∈X"
    have "∃!y. y∈Y ∧ ⟨x, y⟩ ∈ ?f"
    proof
	from A1 A2 show "∃y. y∈Y ∧ ⟨x, y⟩ ∈ ?f"
	by simp
    next fix y y1 assume "y∈Y ∧ ⟨x, y⟩ ∈ ?f"
	and "y1∈Y ∧ ⟨x, y1⟩ ∈ ?f"
      then show "y = y1" by simp
    qed
  } then have "∀x∈X. ∃!y. y∈Y ∧ ⟨ x,y⟩ ∈ ?f"
    by simp
  moreover from A1 have "?f ⊆ X×Y" by auto
  ultimately show ?thesis using func1_1_L11
    by simp
qed
 
text‹The value of a function defined by a meta-function is this 
  meta-function.›

lemma func1_1_L11B: 
  assumes A1: "f:X→Y"   "x∈X"
  and A2: "f = {⟨ x,y⟩ ∈ X×Y. b(x) = y}"
  shows "f`(x) = b(x)"
proof -
  from A1 have "⟨ x,f`(x)⟩ ∈ f" using apply_iff by simp
  with A2 show ?thesis by simp
qed

text‹The next lemma will replace ‹func1_1_L11B› one day.›

lemma ZF_fun_from_tot_val: 
  assumes A1: "f:X→Y"   "x∈X"
  and A2: "f = {⟨x,b(x)⟩. x∈X}"
  shows "f`(x) = b(x)"
proof -
  from A1 have "⟨ x,f`(x)⟩ ∈ f" using apply_iff by simp
   with A2 show ?thesis by simp
qed

text‹Identical meaning as ‹ ZF_fun_from_tot_val›, but
  phrased a bit differently.›

lemma ZF_fun_from_tot_val0: 
  assumes "f:X→Y" and "f = {⟨x,b(x)⟩. x∈X}"
  shows "∀x∈X. f`(x) = b(x)"
  using assms ZF_fun_from_tot_val by simp

text‹Another way of expressing that lambda expression is a function.›

lemma lam_is_fun_range: assumes "f={⟨x,g(x)⟩. x∈X}"
  shows "f:X→range(f)"
proof -
  have "∀x∈X. g(x) ∈ range({⟨x,g(x)⟩. x∈X})" unfolding range_def 
    by auto
  then have "{⟨x,g(x)⟩. x∈X} : X→range({⟨x,g(x)⟩. x∈X})" by (rule ZF_fun_from_total)
  with assms show ?thesis by auto
qed

text‹Yet another way of expressing value of a function.›

lemma ZF_fun_from_tot_val1:
  assumes "x∈X" shows "{⟨x,b(x)⟩. x∈X}`(x)=b(x)"
proof -
  let ?f = "{⟨x,b(x)⟩. x∈X}"
  have "?f:X→range(?f)" using lam_is_fun_range by simp
  with assms show ?thesis using ZF_fun_from_tot_val0 by simp
qed

text‹We can extend a function by specifying its values on a set
  disjoint with the domain.›

lemma func1_1_L11C: assumes A1: "f:X→Y" and A2: "∀x∈A. b(x)∈B"
  and A3: "X∩A = 0" and Dg: "g = f ∪ {⟨x,b(x)⟩. x∈A}"
  shows 
  "g : X∪A → Y∪B"
  "∀x∈X. g`(x) = f`(x)"
  "∀x∈A. g`(x) = b(x)"
proof -
  let ?h = "{⟨x,b(x)⟩. x∈A}"
  from A1 A2 A3 have 
    I: "f:X→Y"  "?h : A→B"  "X∩A = 0"
    using ZF_fun_from_total by auto
  then have "f∪?h : X∪A → Y∪B"
    by (rule fun_disjoint_Un)
  with Dg show "g : X∪A → Y∪B" by simp
  { fix x assume A4: "x∈A"
    with A1 A3 have "(f∪?h)`(x) = ?h`(x)"
      using func1_1_L1 fun_disjoint_apply2
      by blast
    moreover from I A4 have "?h`(x) = b(x)"
      using ZF_fun_from_tot_val by simp
    ultimately have "(f∪?h)`(x) = b(x)"
      by simp
  } with Dg show "∀x∈A. g`(x) = b(x)" by simp
  { fix x assume A5: "x∈X"
    with A3 I have "x ∉ domain(?h)"
      using func1_1_L1 by auto
    then have "(f∪?h)`(x) = f`(x)"
      using fun_disjoint_apply1 by simp
  } with Dg show "∀x∈X. g`(x) = f`(x)" by simp
qed

text‹We can extend a function by specifying its value at a point that
  does not belong to the domain.›

lemma func1_1_L11D: assumes A1: "f:X→Y" and A2: "a∉X"
  and Dg: "g = f ∪ {⟨a,b⟩}"
  shows 
  "g : X∪{a} → Y∪{b}"
  "∀x∈X. g`(x) = f`(x)"
  "g`(a) = b"
proof -
  let ?h = "{⟨a,b⟩}"
  from A1 A2 Dg have I:
    "f:X→Y"  "∀x∈{a}. b∈{b}"  "X∩{a} = 0"  "g = f ∪ {⟨x,b⟩. x∈{a}}"
    by auto
  then show "g : X∪{a} → Y∪{b}"
    by (rule func1_1_L11C)
  from I show "∀x∈X. g`(x) = f`(x)"
    by (rule func1_1_L11C)
  from I have "∀x∈{a}. g`(x) = b"
    by (rule func1_1_L11C)
  then show "g`(a) = b" by auto
qed

text‹A technical lemma about extending a function both by defining
  on a set disjoint with the domain and on a point that does not belong
  to any of those sets.›

lemma func1_1_L11E:
  assumes A1: "f:X→Y" and 
  A2: "∀x∈A. b(x)∈B" and 
  A3: "X∩A = 0" and A4: "a∉ X∪A"
  and Dg: "g = f ∪ {⟨x,b(x)⟩. x∈A} ∪ {⟨a,c⟩}"
  shows
  "g : X∪A∪{a} → Y∪B∪{c}"
  "∀x∈X. g`(x) = f`(x)"
  "∀x∈A. g`(x) = b(x)"
  "g`(a) = c"
proof -
  let ?h = "f ∪ {⟨x,b(x)⟩. x∈A}"
  from assms show "g : X∪A∪{a} → Y∪B∪{c}"
    using func1_1_L11C func1_1_L11D by simp
  from A1 A2 A3 have I:
    "f:X→Y"  "∀x∈A. b(x)∈B"  "X∩A = 0"  "?h = f ∪ {⟨x,b(x)⟩. x∈A}"
    by auto
  from assms have 
    II: "?h : X∪A → Y∪B"  "a∉ X∪A"  "g = ?h ∪ {⟨a,c⟩}"
    using func1_1_L11C by auto
  then have III: "∀x∈X∪A. g`(x) = ?h`(x)" by (rule func1_1_L11D)
  moreover from I have  "∀x∈X. ?h`(x) = f`(x)"
    by (rule func1_1_L11C)
  ultimately show "∀x∈X. g`(x) = f`(x)" by simp
  from I have "∀x∈A. ?h`(x) = b(x)" by (rule func1_1_L11C)
  with III show "∀x∈A. g`(x) = b(x)" by simp
  from II show "g`(a) = c" by (rule func1_1_L11D)
qed

text‹A way of defining a function on a union of two possibly overlapping sets. We decompose the 
union into two differences and the intersection and define a function separately on each part.›

lemma fun_union_overlap: assumes "∀x∈A∩B. h(x) ∈ Y"  "∀x∈A-B. f(x) ∈ Y"  "∀x∈B-A. g(x) ∈ Y"
  shows "{⟨x,if x∈A-B then f(x) else if x∈B-A then g(x) else h(x)⟩. x ∈ A∪B}: A∪B → Y"
proof -
  let ?F = "{⟨x,if x∈A-B then f(x) else if x∈B-A then g(x) else h(x)⟩. x ∈ A∩B}"
  from assms have "∀x∈A∪B. (if x∈A-B then f(x) else if x∈B-A then g(x) else h(x)) ∈ Y"
    by auto
  then show ?thesis by (rule ZF_fun_from_total)
qed

text‹Inverse image of intersection is the intersection of inverse images.›

lemma invim_inter_inter_invim: assumes "f:X→Y"
  shows "f-``(A∩B) = f-``(A) ∩ f-``(B)"
  using assms fun_is_fun function_vimage_Int by simp

text‹The inverse image of an intersection of a nonempty collection of sets 
  is the intersection of the 
  inverse images. This generalizes ‹invim_inter_inter_invim› 
  which is proven for the case of two sets.›

lemma func1_1_L12:
  assumes A1: "B ⊆ Pow(Y)" and A2: "B≠0" and A3: "f:X→Y"
  shows "f-``(⋂B) = (⋂U∈B. f-``(U))"
proof
  from A2 show  "f-``(⋂B) ⊆ (⋂U∈B. f-``(U))" by blast
  show "(⋂U∈B. f-``(U)) ⊆ f-``(⋂B)"
  proof
    fix x assume A4: "x ∈ (⋂U∈B. f-``(U))"
    from A3 have "∀U∈B. f-``(U) ⊆ X" using func1_1_L6A by simp
    with A4 have "∀U∈B. x∈X" by auto
    with A2 have "x∈X" by auto
    with A3 have "∃!y. ⟨ x,y⟩ ∈ f" using Pi_iff_old by simp
    with A2 A4 show "x ∈ f-``(⋂B)" using vimage_iff by blast
  qed
qed


text‹The inverse image of a set does not change when we intersect
  the set with the image of the domain.›

lemma inv_im_inter_im: assumes "f:X→Y" 
  shows "f-``(A ∩ f``(X)) = f-``(A)"
  using assms invim_inter_inter_invim inv_im_dom func1_1_L6A
  by blast

text‹If the inverse image of a set is not empty, then the set is not empty.
  Proof by contradiction.›

lemma func1_1_L13: assumes A1:"f-``(A) ≠ 0" shows "A≠0"
  using assms by auto

text‹If the image of a set is not empty, then the set is not empty.
  Proof by contradiction.›

lemma func1_1_L13A: assumes A1: "f``(A)≠0" shows "A≠0"
  using assms by auto

text‹What is the inverse image of a singleton?›

lemma func1_1_L14: assumes "f∈X→Y" 
  shows "f-``({y}) = {x∈X. f`(x) = y}" 
  using assms func1_1_L6A vimage_singleton_iff apply_iff by auto

text‹A lemma that can be used instead ‹fun_extension_iff›
  to show that two functions are equal›

lemma func_eq: assumes "f: X→Y"  "g: X→Z"
  and  "∀x∈X. f`(x) = g`(x)"
  shows "f = g" using assms fun_extension_iff by simp

text‹Function defined on a singleton is a single pair.›

lemma func_singleton_pair: assumes A1: "f : {a}→X"
  shows "f = {⟨a, f`(a)⟩}"
proof -
  let ?g = "{⟨a, f`(a)⟩}"
  note A1
  moreover have "?g : {a} → {f`(a)}" using singleton_fun by simp
  moreover have "∀x ∈ {a}. f`(x) = ?g`(x)" using singleton_apply
    by simp
  ultimately show "f = ?g" by (rule func_eq)
qed

text‹A single pair is a function on a singleton. This is
  similar to ‹singleton_fun› from standard Isabelle/ZF.›

lemma pair_func_singleton: assumes A1: "y ∈ Y"
  shows "{⟨x,y⟩} : {x} → Y"
proof -
  have "{⟨x,y⟩} : {x} → {y}" using singleton_fun by simp
  moreover from A1 have "{y} ⊆ Y" by simp
  ultimately show "{⟨x,y⟩} : {x} → Y"
    by (rule func1_1_L1B)
qed

text‹The value of a pair on the first element is the second one.›

lemma pair_val: shows "{⟨x,y⟩}`(x) = y"
  using singleton_fun apply_equality by simp
  
text‹A more familiar definition of inverse image.›

lemma func1_1_L15: assumes A1: "f:X→Y"
  shows "f-``(A) = {x∈X. f`(x) ∈ A}"
proof -
  have "f-``(A) = (⋃y∈A . f-``{y})" 
    by (rule vimage_eq_UN)
  with A1 show ?thesis using func1_1_L14 by auto
qed

text‹A more familiar definition of image.›

lemma func_imagedef: assumes A1: "f:X→Y" and A2: "A⊆X"
  shows "f``(A) = {f`(x). x ∈ A}"
proof
  from A1 show "f``(A) ⊆ {f`(x). x ∈ A}"
    using image_iff apply_iff by auto
  show "{f`(x). x ∈ A} ⊆ f``(A)"
  proof
    fix y assume "y ∈ {f`(x). x ∈ A}"
    then obtain x where "x∈A" and  "y = f`(x)"
      by auto
    with A1 A2 have "⟨x,y⟩ ∈ f" using apply_iff by force  
    with A1 A2 ‹x∈A› show "y ∈ f``(A)" using image_iff by auto
  qed
qed

text‹The image of a set contained in domain under identity is the same set.›

lemma image_id_same: assumes "A⊆X" shows "id(X)``(A) = A"
  using assms id_type id_conv by auto

text‹The inverse image of a set contained in domain under identity is the same set.›

lemma vimage_id_same: assumes "A⊆X" shows "id(X)-``(A) = A"
  using assms id_type id_conv by auto

text‹What is the image of a singleton?›

lemma singleton_image: 
  assumes "f∈X→Y" and "x∈X"
  shows "f``{x} = {f`(x)}"
  using assms func_imagedef by auto

text‹If an element of the domain of a function belongs to a set, 
  then its value belongs to the imgage of that set.›

lemma func1_1_L15D: assumes "f:X→Y"  "x∈A"  "A⊆X"
  shows "f`(x) ∈ f``(A)"
  using assms func_imagedef by auto

text‹Range is the image of the domain. Isabelle/ZF defines
  ‹range(f)› as ‹domain(converse(f))›,
  and that's why we have something to prove here.›

lemma range_image_domain: 
  assumes A1: "f:X→Y" shows "f``(X) = range(f)"
proof
  show "f``(X) ⊆ range(f)" using image_def by auto
  { fix y assume "y ∈ range(f)"
    then obtain x where "⟨y,x⟩ ∈ converse(f)" by auto
    with A1 have "x∈X" using func1_1_L5 by blast
    with A1 have "f`(x) ∈ f``(X)" using func_imagedef
      by auto
    with A1  ‹⟨y,x⟩ ∈ converse(f)› have "y ∈ f``(X)"
      using apply_equality by auto
  } then show "range(f) ⊆ f``(X)" by auto
qed
    
text‹The difference of images is contained in the image of difference.›

lemma diff_image_diff: assumes A1: "f: X→Y" and A2: "A⊆X"
  shows "f``(X) - f``(A) ⊆ f``(X-A)"
proof
  fix y assume "y ∈ f``(X) - f``(A)"
  hence "y ∈ f``(X)" and I: "y ∉ f``(A)" by auto
  with A1 obtain x where "x∈X" and II: "y = f`(x)"
    using func_imagedef by auto
  with A1 A2 I have "x∉A"
    using func1_1_L15D by auto
  with ‹x∈X› have "x ∈ X-A" "X-A ⊆ X" by auto
  with A1 II show "y ∈ f``(X-A)"
    using func1_1_L15D by simp
qed

text‹The image of an intersection is contained in the 
  intersection of the images.›

lemma image_of_Inter: assumes  A1: "f:X→Y" and
  A2: "I≠0" and A3: "∀i∈I. P(i) ⊆ X"
  shows "f``(⋂i∈I. P(i)) ⊆ ( ⋂i∈I. f``(P(i)) )"
proof
  fix y assume A4: "y ∈ f``(⋂i∈I. P(i))"
  from A1 A2 A3 have "f``(⋂i∈I. P(i)) = {f`(x). x ∈ ( ⋂i∈I. P(i) )}"
    using ZF1_1_L7 func_imagedef by simp
  with A4 obtain x where "x ∈ ( ⋂i∈I. P(i) )" and "y = f`(x)"
    by auto
  with A1 A2 A3 show "y ∈ ( ⋂i∈I. f``(P(i)) )" using func_imagedef
    by auto
qed

text‹The image of union is the union of images.›

lemma image_of_Union: assumes A1: "f:X→Y" and A2: "∀A∈M. A⊆X"
  shows "f``(⋃M) = ⋃{f``(A). A∈M}"
proof
  from A2 have "⋃M ⊆ X" by auto
  { fix y assume "y ∈ f``(⋃M)"
    with A1 ‹⋃M ⊆ X› obtain x where "x∈⋃M" and I: "y = f`(x)" 
      using func_imagedef by auto
    then obtain A where "A∈M" and "x∈A" by auto
    with assms I have "y ∈ ⋃{f``(A). A∈M}" using func_imagedef by auto
  } thus "f``(⋃M) ⊆ ⋃{f``(A). A∈M}" by auto
  { fix y assume "y ∈ ⋃{f``(A). A∈M}"
    then obtain A where "A∈M" and "y ∈ f``(A)" by auto
    with assms ‹⋃M ⊆ X› have "y ∈ f``(⋃M)" using func_imagedef by auto
  } thus "⋃{f``(A). A∈M} ⊆ f``(⋃M)" by auto
qed

text‹The image of a nonempty subset of domain is nonempty.›

lemma func1_1_L15A: 
  assumes A1: "f: X→Y" and A2: "A⊆X" and A3: "A≠0"
  shows "f``(A) ≠ 0"
proof -
  from A3 obtain x where "x∈A" by auto
  with A1 A2 have "f`(x) ∈ f``(A)"
    using func_imagedef by auto
  then show "f``(A) ≠ 0" by auto
qed

text‹The next lemma allows to prove statements about the values in the
  domain of a function given a statement about values in the range.›

lemma func1_1_L15B: 
  assumes "f:X→Y" and "A⊆X" and "∀y∈f``(A). P(y)"
  shows "∀x∈A. P(f`(x))"
  using assms func_imagedef by simp
  
text‹An image of an image is the image of a composition.›

lemma func1_1_L15C: assumes  A1: "f:X→Y" and A2: "g:Y→Z"
  and A3: "A⊆X"
  shows 
  "g``(f``(A)) =  {g`(f`(x)). x∈A}"
  "g``(f``(A)) = (g O f)``(A)"
proof -
  from A1 A3 have "{f`(x). x∈A} ⊆ Y"
    using apply_funtype by auto
  with A2 have "g``{f`(x). x∈A} = {g`(f`(x)). x∈A}"
    using func_imagedef by auto
  with A1 A3 show I: "g``(f``(A)) =  {g`(f`(x)). x∈A}" 
    using func_imagedef by simp
  from A1 A3 have "∀x∈A. (g O f)`(x) = g`(f`(x))"
    using comp_fun_apply by auto
  with I have "g``(f``(A)) = {(g O f)`(x). x∈A}"
    by simp
  moreover from A1 A2 A3 have "(g O f)``(A) = {(g O f)`(x). x∈A}"
    using comp_fun func_imagedef by blast
  ultimately show "g``(f``(A)) = (g O f)``(A)"
    by simp
qed
 
text‹What is the image of a set defined by a meta-fuction?›

lemma func1_1_L17: 
  assumes A1: "f ∈ X→Y" and A2: "∀x∈A. b(x) ∈ X"
  shows "f``({b(x). x∈A}) = {f`(b(x)). x∈A}"
proof -
  from A2 have "{b(x). x∈A} ⊆ X" by auto
  with A1 show ?thesis using func_imagedef by auto
qed

text‹What are the values of composition of three functions?›

lemma func1_1_L18: assumes A1: "f:A→B"  "g:B→C"  "h:C→D"
  and A2: "x∈A"
  shows
  "(h O g O f)`(x) ∈ D"
  "(h O g O f)`(x) = h`(g`(f`(x)))"  
proof -
  from A1 have "(h O g O f) : A→D"
    using comp_fun by blast
  with A2 show "(h O g O f)`(x) ∈ D" using apply_funtype
    by simp
  from A1 A2 have "(h O g O f)`(x) = h`( (g O f)`(x))"
    using comp_fun comp_fun_apply by blast
  with A1 A2 show "(h O g O f)`(x) = h`(g`(f`(x)))"
    using comp_fun_apply by simp
qed

text‹A composition of functions is a function. This is a slight
  generalization of standard Isabelle's ‹comp_fun›
›

lemma comp_fun_subset: 
  assumes A1: "g:A→B"  and A2: "f:C→D" and A3: "B ⊆ C"
  shows "f O g : A → D"
proof -
  from A1 A3 have "g:A→C" by (rule func1_1_L1B) 
  with A2 show "f O g : A → D" using comp_fun by simp
qed

text‹This lemma supersedes the lemma ‹comp_eq_id_iff› 
  in Isabelle/ZF. Contributed by Victor Porton.›

lemma comp_eq_id_iff1: assumes A1: "g: B→A" and A2: "f: A→C"
  shows "(∀y∈B. f`(g`(y)) = y) ⟷ f O g = id(B)"
proof -
  from assms have "f O g: B→C" and "id(B): B→B"
    using comp_fun id_type by auto
  then have "(∀y∈B. (f O g)`y = id(B)`(y)) ⟷ f O g = id(B)" 
    by (rule fun_extension_iff)
  moreover from A1 have 
    "∀y∈B. (f O g)`y = f`(g`y)" and "∀y∈B. id(B)`(y) = y"
    by auto
  ultimately show "(∀y∈B. f`(g`y) = y) ⟷ f O g = id(B)" by simp
qed
  
text‹A lemma about a value of a function that is a union of 
  some collection of functions.›

lemma fun_Union_apply: assumes A1: "⋃F : X→Y" and 
  A2: "f∈F" and A3: "f:A→B" and A4: "x∈A"
  shows "(⋃F)`(x) = f`(x)"
proof -
  from A3 A4 have "⟨x, f`(x)⟩ ∈ f" using apply_Pair
    by simp
  with A2 have "⟨x, f`(x)⟩ ∈ ⋃F" by auto
  with A1 show "(⋃F)`(x) = f`(x)" using apply_equality
    by simp
qed

subsection‹Functions restricted to a set›

text‹Standard Isabelle/ZF defines the notion ‹restrict(f,A)› 
  of to mean a function (or relation) $f$ restricted to a set.
  This means that if $f$ is a function defined on $X$ and $A$
  is a subset of $X$ then ‹restrict(f,A)› is a function 
  whith the same values as $f$, but whose domain is $A$.›
 
text‹What is the inverse image of a set under a restricted fuction?›

lemma func1_2_L1: assumes A1: "f:X→Y" and A2: "B⊆X"
  shows "restrict(f,B)-``(A) = f-``(A) ∩ B"
proof -
  let ?g = "restrict(f,B)"
  from A1 A2 have "?g:B→Y" 
    using restrict_type2 by simp
  with A2 A1 show "?g-``(A) = f-``(A) ∩ B"
    using func1_1_L15 restrict_if by auto
qed
   
text‹A criterion for when one function is a restriction of another.
  The lemma below provides a result useful in the actual proof of the 
  criterion and applications.›

lemma func1_2_L2: 
  assumes A1: "f:X→Y" and A2: "g ∈ A→Z" 
  and A3: "A⊆X" and A4: "f ∩ A×Z = g"
  shows "∀x∈A. g`(x) = f`(x)"
proof
  fix x assume "x∈A"
  with A2 have "⟨ x,g`(x)⟩ ∈ g" using apply_Pair by simp
  with A4 A1 show "g`(x) = f`(x)"  using apply_iff by auto 
qed

text‹Here is the actual criterion.›

lemma func1_2_L3: 
  assumes A1: "f:X→Y" and A2: "g:A→Z" 
  and A3: "A⊆X" and A4: "f ∩ A×Z = g"
  shows "g = restrict(f,A)"
proof
  from A4 show "g ⊆ restrict(f, A)" using restrict_iff by auto
  show "restrict(f, A) ⊆ g"
  proof
    fix z assume A5:"z ∈ restrict(f,A)"
    then obtain x y where D1:"z∈f ∧ x∈A  ∧ z = ⟨x,y⟩"
      using restrict_iff by auto
    with A1 have "y = f`(x)" using apply_iff by auto
    with A1 A2 A3 A4 D1 have "y = g`(x)" using func1_2_L2 by simp
    with A2 D1 show "z∈g" using apply_Pair by simp
  qed
qed

text‹Which function space a restricted function belongs to?›

lemma func1_2_L4: 
  assumes A1: "f:X→Y" and A2: "A⊆X" and A3: "∀x∈A. f`(x) ∈ Z"
  shows "restrict(f,A) : A→Z"
proof -
  let ?g = "restrict(f,A)"
  from A1 A2 have "?g : A→Y" 
    using restrict_type2 by simp
  moreover { 
    fix x assume "x∈A" 
    with A1 A3 have "?g`(x) ∈ Z" using restrict by simp}
  ultimately show ?thesis by (rule Pi_type)
qed

text‹A simpler case of ‹func1_2_L4›, where
  the range of the original and restricted function are the same.
›

corollary restrict_fun: assumes A1: "f:X→Y" and A2: "A⊆X"
  shows "restrict(f,A) : A → Y"
proof -
  from assms have "∀x∈A. f`(x) ∈ Y" using apply_funtype
    by auto
  with assms show ?thesis using func1_2_L4 by simp
qed

text‹A composition of two functions is the same as 
  composition with a restriction.›

lemma comp_restrict: 
  assumes A1: "f : A→B" and A2: "g : X → C" and A3: "B⊆X"
  shows "g O f = restrict(g,B) O f"
proof -
  from assms have "g O f : A → C" using comp_fun_subset
    by simp
  moreover from assms have "restrict(g,B) O f : A → C"
    using restrict_fun comp_fun by simp
  moreover from A1 have 
    "∀x∈A. (g O f)`(x) = (restrict(g,B) O f)`(x)"
    using comp_fun_apply apply_funtype restrict
    by simp
  ultimately show "g O f = restrict(g,B) O f"
    by (rule func_eq)
qed

text‹A way to look at restriction. Contributed by Victor Porton.›

lemma right_comp_id_any: shows "r O id(C) = restrict(r,C)"
  unfolding restrict_def by auto
 
subsection‹Constant functions›

text‹Constant functions are trivial, but still we need to 
  prove some properties to shorten proofs.›

text‹We define constant($=c$) functions on a set $X$ 
  in a natural way as ConstantFunction$(X,c)$.›

definition
  "ConstantFunction(X,c) ≡ X×{c}"

text‹Constant function belongs to the function space.›

lemma func1_3_L1: 
  assumes A1: "c∈Y" shows "ConstantFunction(X,c) : X→Y"
proof -
   from A1 have "X×{c} = {⟨ x,y⟩ ∈ X×Y. c = y}" 
     by auto
   with A1 show ?thesis using func1_1_L11A ConstantFunction_def
     by simp
qed

text‹Constant function is equal to the constant on its domain.›

lemma func1_3_L2: assumes A1: "x∈X"
  shows "ConstantFunction(X,c)`(x) = c"
proof -
  have "ConstantFunction(X,c) ∈ X→{c}"
    using func1_3_L1 by simp
  moreover from A1 have "⟨ x,c⟩ ∈ ConstantFunction(X,c)"
    using ConstantFunction_def by simp
  ultimately show ?thesis using apply_iff by simp
qed

subsection‹Injections, surjections, bijections etc.›

text‹In this section we prove the properties of the spaces
  of injections, surjections and bijections that we can't find in the
  standard Isabelle's ‹Perm.thy›.›

text‹For injections the image a difference of two sets is
  the difference of images›

lemma inj_image_dif: 
  assumes A1: "f ∈ inj(A,B)" and A2: "C ⊆ A"
  shows "f``(A-C) = f``(A) - f``(C)"
proof
  show "f``(A - C) ⊆ f``(A) - f``(C)"
  proof
    fix y assume A3: "y ∈ f``(A - C)"
    from A1 have "f:A→B" using inj_def by simp
    moreover have "A-C ⊆ A" by auto
    ultimately have "f``(A-C) = {f`(x). x ∈ A-C}"
      using func_imagedef by simp
    with A3 obtain x where I: "f`(x) = y" and "x ∈ A-C" 
      by auto
    hence "x∈A" by auto
    with ‹f:A→B› I have "y ∈ f``(A)"
      using func_imagedef by auto
    moreover have "y ∉  f``(C)"
    proof -
      { assume "y ∈ f``(C)"
	with A2 ‹f:A→B› obtain x⇩0 
	  where II: "f`(x⇩0) = y" and "x⇩0 ∈ C"
	  using func_imagedef by auto
	with A1 A2 I ‹x∈A› have
	  "f ∈ inj(A,B)" "f`(x) = f`(x⇩0)"  "x∈A" "x⇩0 ∈ A"
	  by auto
	then have "x = x⇩0" by (rule inj_apply_equality)
	with ‹x ∈ A-C› ‹x⇩0 ∈ C› have False by simp
      } thus ?thesis by auto
    qed
    ultimately show "y ∈ f``(A) - f``(C)" by simp
  qed
  from A1 A2 show "f``(A) - f``(C) ⊆ f``(A-C)"
    using inj_def diff_image_diff by auto
qed

text‹For injections the image of intersection is the intersection of images.›

lemma inj_image_inter: assumes A1: "f ∈ inj(X,Y)" and A2: "A⊆X" "B⊆X"
  shows "f``(A∩B) = f``(A) ∩ f``(B)"
proof
  show "f``(A∩B) ⊆ f``(A) ∩ f``(B)" using image_Int_subset by simp
  { from A1 have "f:X→Y" using inj_def by simp 
    fix y assume "y ∈ f``(A) ∩ f``(B)"
    then have "y ∈ f``(A)" and  "y ∈ f``(B)" by auto
    with A2 ‹f:X→Y› obtain x⇩A x⇩B where 
    "x⇩A ∈ A" "x⇩B ∈ B" and I: "y = f`(x⇩A)"  "y = f`(x⇩B)"
      using func_imagedef by auto
    with A2 have "x⇩A ∈ X" "x⇩B ∈ X" and " f`(x⇩A) =  f`(x⇩B)" by auto 
    with A1 have "x⇩A = x⇩B" using inj_def by auto
    with ‹x⇩A ∈ A› ‹x⇩B ∈ B› have "f`(x⇩A) ∈ {f`(x). x ∈ A∩B}" by auto
    moreover from A2 ‹f:X→Y› have "f``(A∩B) = {f`(x). x ∈ A∩B}"
      using func_imagedef by blast
    ultimately have "f`(x⇩A) ∈ f``(A∩B)" by simp 
    with I have "y ∈ f``(A∩B)" by simp 
  } thus "f``(A) ∩ f``(B) ⊆ f``(A ∩ B)" by auto
qed

text‹For surjection from $A$ to $B$ the image of 
  the domain is $B$.›

lemma surj_range_image_domain: assumes A1: "f ∈ surj(A,B)"
  shows "f``(A) = B"
proof -
  from A1 have "f``(A) = range(f)" 
    using surj_def range_image_domain by auto
  with A1 show "f``(A) = B"  using surj_range
    by simp
qed

text‹For injections the inverse image of an image is the same set.›

lemma inj_vimage_image: assumes "f ∈ inj(X,Y)" and "A⊆X"
  shows "f-``(f``(A)) = A"
proof -
  have "f-``(f``(A)) = (converse(f) O f)``(A)" 
    using vimage_converse image_comp by simp
  with assms show ?thesis using left_comp_inverse image_id_same
    by simp
qed

text‹For surjections the image of an inverse image is the same set.›

lemma surj_image_vimage: assumes A1: "f ∈ surj(X,Y)" and A2: "A⊆Y"
  shows "f``(f-``(A)) = A"
proof -
  have "f``(f-``(A)) = (f O converse(f))``(A)"
    using vimage_converse image_comp by simp
  with assms show ?thesis using right_comp_inverse image_id_same
    by simp
qed

text‹A lemma about how a surjection maps collections of subsets in domain and rangge.›

lemma surj_subsets: assumes A1: "f ∈ surj(X,Y)" and A2: "B ⊆ Pow(Y)"
  shows "{ f``(U). U ∈ {f-``(V). V∈B} } = B"
proof
  { fix W assume "W ∈ { f``(U). U ∈ {f-``(V). V∈B} }"
    then obtain U where I: "U ∈ {f-``(V). V∈B}" and II: "W = f``(U)" by auto
    then obtain V where "V∈B" and "U = f-``(V)" by auto
    with II have "W = f``(f-``(V))" by simp
    moreover from assms ‹V∈B› have "f ∈ surj(X,Y)" and "V⊆Y" by auto 
    ultimately have "W=V" using surj_image_vimage by simp
    with ‹V∈B› have "W ∈ B" by simp 
  } thus "{ f``(U). U ∈ {f-``(V). V∈B} } ⊆ B" by auto
  { fix W assume "W∈B"
    let ?U = "f-``(W)"
    from ‹W∈B› have "?U ∈ {f-``(V). V∈B}" by auto
    moreover from A1 A2 ‹W∈B› have "W = f``(?U)" using surj_image_vimage by auto  
    ultimately have "W ∈ { f``(U). U ∈ {f-``(V). V∈B} }" by auto 
  } thus "B ⊆ { f``(U). U ∈ {f-``(V). V∈B} }" by auto
qed

text‹Restriction of an bijection to a set without a point
  is a a bijection.›

lemma bij_restrict_rem: 
  assumes A1: "f ∈ bij(A,B)" and A2: "a∈A"
  shows "restrict(f, A-{a}) ∈ bij(A-{a}, B-{f`(a)})"
proof -
  let ?C = "A-{a}"
  from A1 have "f ∈ inj(A,B)"  "?C ⊆ A"
    using bij_def by auto
  then have "restrict(f,?C) ∈ bij(?C, f``(?C))"
    using restrict_bij by simp
  moreover have "f``(?C) =  B-{f`(a)}"
  proof -
    from A2 ‹f ∈ inj(A,B)› have "f``(?C) = f``(A) - f``{a}"
      using inj_image_dif by simp
    moreover from A1 have "f``(A) = B" 
      using bij_def surj_range_image_domain by auto
    moreover from A1 A2 have "f``{a} = {f`(a)}"
      using bij_is_fun singleton_image by blast
    ultimately show "f``(?C) =  B-{f`(a)}" by simp
  qed
  ultimately show ?thesis by simp
qed

text‹The domain of a bijection between $X$ and $Y$ is $X$.›

lemma domain_of_bij: 
  assumes A1: "f ∈ bij(X,Y)" shows "domain(f) = X"
proof -
  from A1 have "f:X→Y" using bij_is_fun by simp
  then show "domain(f) = X" using func1_1_L1 by simp
qed

text‹The value of the inverse of an injection on a point of the image 
  of a set belongs to that set.›

lemma inj_inv_back_in_set: 
  assumes A1: "f ∈ inj(A,B)" and A2: "C⊆A" and A3: "y ∈ f``(C)"
  shows 
  "converse(f)`(y) ∈ C"
  "f`(converse(f)`(y)) = y"
proof -
  from A1 have I: "f:A→B" using inj_is_fun by simp
  with A2 A3 obtain x where II: "x∈C"   "y = f`(x)"
    using func_imagedef by auto
  with A1 A2 show "converse(f)`(y) ∈ C" using left_inverse
    by auto
  from A1 A2 I II show "f`(converse(f)`(y)) = y"
    using func1_1_L5A right_inverse by auto
qed

text‹For injections if a value at a point 
  belongs to the image of a set, then the point
  belongs to the set.›

lemma inj_point_of_image: 
  assumes A1: "f ∈ inj(A,B)" and A2: "C⊆A" and
  A3: "x∈A" and A4: "f`(x) ∈ f``(C)"
  shows "x ∈ C"
proof -
  from A1 A2 A4 have "converse(f)`(f`(x)) ∈ C"
    using inj_inv_back_in_set by simp
  moreover from A1 A3 have "converse(f)`(f`(x)) = x"
    using left_inverse_eq by simp
  ultimately show "x ∈ C" by simp
qed

text‹For injections the image of intersection is 
  the intersection of images.›

lemma inj_image_of_Inter: assumes A1: "f ∈ inj(A,B)" and
  A2: "I≠0" and A3: "∀i∈I. P(i) ⊆ A"
  shows "f``(⋂i∈I. P(i)) = ( ⋂i∈I. f``(P(i)) )"
proof
  from A1 A2 A3 show "f``(⋂i∈I. P(i)) ⊆ ( ⋂i∈I. f``(P(i)) )"
    using inj_is_fun image_of_Inter by auto
  from A1 A2 A3 have "f:A→B"  and "( ⋂i∈I. P(i) ) ⊆ A"
    using inj_is_fun ZF1_1_L7 by auto
  then have I: "f``(⋂i∈I. P(i)) = { f`(x). x ∈ ( ⋂i∈I. P(i) ) }"
    using func_imagedef by simp
  { fix y assume A4: "y ∈ ( ⋂i∈I. f``(P(i)) )"
    let ?x = "converse(f)`(y)"
    from A2 obtain i⇩0 where "i⇩0 ∈ I" by auto
    with A1 A4 have II: "y ∈ range(f)" using inj_is_fun func1_1_L6
      by auto
    with A1 have III: "f`(?x) = y" using right_inverse by simp
    from A1 II have IV: "?x ∈ A" using inj_converse_fun apply_funtype 
      by blast
    { fix i assume "i∈I"
      with A3 A4 III have "P(i) ⊆ A" and "f`(?x) ∈  f``(P(i))" 
	by auto
      with A1 IV have "?x ∈ P(i)" using inj_point_of_image
	by blast
    } then have "∀i∈I. ?x ∈ P(i)" by simp
    with A2 I have "f`(?x) ∈ f``( ⋂i∈I. P(i) )"
      by auto
    with III have "y ∈  f``( ⋂i∈I. P(i) )" by simp
  } then show "( ⋂i∈I. f``(P(i)) ) ⊆  f``( ⋂i∈I. P(i) )"
    by auto
qed

text‹An injection is injective onto its range. Suggested by Victor Porton.›

lemma inj_inj_range: assumes "f ∈ inj(A,B)"
  shows "f ∈ inj(A,range(f))"
  using assms inj_def range_of_fun by auto


text‹An injection is a bijection on its range. Suggested by Victor Porton.›

lemma inj_bij_range: assumes "f ∈ inj(A,B)" 
  shows "f ∈ bij(A,range(f))"
proof -
  from assms have "f ∈ surj(A,range(f))" using inj_def fun_is_surj
    by auto
  with assms show ?thesis using inj_inj_range bij_def by simp
qed
  
text‹A lemma about extending a surjection by one point.›

lemma surj_extend_point: 
  assumes A1: "f ∈ surj(X,Y)" and A2: "a∉X" and
  A3: "g = f ∪ {⟨a,b⟩}"
  shows "g ∈ surj(X∪{a},Y∪{b})"
proof -
  from A1 A2 A3 have "g : X∪{a} → Y∪{b}"
    using surj_def func1_1_L11D by simp
  moreover have "∀y ∈ Y∪{b}. ∃x ∈ X∪{a}. y = g`(x)"
  proof
    fix y assume "y ∈  Y ∪ {b}"
    then have "y ∈ Y ∨ y = b" by auto
    moreover
    { assume "y ∈ Y"
      with A1 obtain x where "x∈X" and "y = f`(x)"
	using surj_def by auto
      with A1 A2 A3 have "x ∈  X∪{a}" and "y = g`(x)"
	using surj_def func1_1_L11D by auto
      then have "∃x ∈ X∪{a}. y = g`(x)" by auto }
    moreover
    { assume "y = b"
      with A1 A2 A3 have "y = g`(a)"
	using surj_def func1_1_L11D by auto
      then have "∃x ∈ X∪{a}. y = g`(x)" by auto }
    ultimately show "∃x ∈ X∪{a}. y = g`(x)"
      by auto
  qed
  ultimately show "g ∈ surj(X∪{a},Y∪{b})"
    using surj_def by auto
qed

text‹A lemma about extending an injection by one point. 
  Essentially the same as standard Isabelle's ‹inj_extend›.
›

lemma inj_extend_point: assumes "f ∈ inj(X,Y)" "a∉X" "b∉Y"
  shows "(f ∪ {⟨a,b⟩}) ∈ inj(X∪{a},Y∪{b})"
proof -
  from assms have "cons(⟨a,b⟩,f) ∈ inj(cons(a, X), cons(b, Y))"
    using assms inj_extend by simp
  moreover have "cons(⟨a,b⟩,f) = f ∪ {⟨a,b⟩}" and
    "cons(a, X) = X∪{a}" and "cons(b, Y) = Y∪{b}"
    by auto
  ultimately show ?thesis by simp
qed

text‹A lemma about extending a bijection by one point.›

lemma bij_extend_point: assumes "f ∈ bij(X,Y)" "a∉X" "b∉Y"
  shows "(f ∪ {⟨a,b⟩}) ∈ bij(X∪{a},Y∪{b})"
  using assms surj_extend_point inj_extend_point bij_def
  by simp

text‹A quite general form of the $a^{-1}b = 1$ 
  implies $a=b$ law.›

lemma comp_inv_id_eq: 
  assumes A1: "converse(b) O a = id(A)" and
  A2: "a ⊆ A×B" "b ∈ surj(A,B)"
  shows "a = b"
proof -
  from A1 have "(b O converse(b)) O a = b O id(A)"
    using comp_assoc by simp
  with A2 have "id(B) O a = b O id(A)" 
    using right_comp_inverse by simp
  moreover
  from A2 have "a ⊆ A×B" and "b ⊆ A×B"
    using surj_def fun_subset_prod
    by auto
  then have "id(B) O a = a" and "b O id(A) = b"
    using left_comp_id right_comp_id by auto
  ultimately show "a = b" by simp
qed

text‹A special case of ‹comp_inv_id_eq› - 
  the $a^{-1}b = 1$ implies $a=b$ law for bijections.›

lemma comp_inv_id_eq_bij: 
  assumes A1: "a ∈ bij(A,B)" "b ∈ bij(A,B)" and
  A2: "converse(b) O a = id(A)"
  shows "a = b"
proof -
  from A1 have  "a ⊆ A×B" and "b ∈ surj(A,B)"
    using bij_def surj_def fun_subset_prod
    by auto
  with A2 show "a = b" by (rule comp_inv_id_eq)
qed

text‹Converse of a converse of a bijection is the same bijection. 
This is a special case of ‹converse_converse› from standard Isabelle's 
‹equalities› theory where it is proved for relations.›

lemma bij_converse_converse: assumes "a ∈ bij(A,B)" 
  shows "converse(converse(a)) = a"
proof -
  from assms have "a ⊆ A×B" using bij_def surj_def fun_subset_prod by simp
  then show ?thesis using converse_converse by simp
qed

text‹If a composition of bijections is identity, then one is the inverse
  of the other.›

lemma comp_id_conv: assumes A1: "a ∈ bij(A,B)" "b ∈ bij(B,A)" and
  A2: "b O a = id(A)"
  shows "a = converse(b)" and "b = converse(a)"
proof -
  from A1 have "a ∈ bij(A,B)" and "converse(b) ∈ bij(A,B)" using bij_converse_bij 
    by auto
  moreover from assms have "converse(converse(b)) O a = id(A)" 
    using bij_converse_converse by simp
  ultimately show "a = converse(b)" by (rule comp_inv_id_eq_bij)
  with assms show "b = converse(a)" using bij_converse_converse by simp
qed

text‹A version of ‹comp_id_conv› with weaker assumptions.›

lemma comp_conv_id: assumes A1: "a ∈ bij(A,B)" and A2: "b:B→A" and
  A3: "∀x∈A. b`(a`(x)) = x"
  shows "b ∈ bij(B,A)" and  "a = converse(b)" and "b = converse(a)"
proof -
  have "b ∈ surj(B,A)"
  proof -
    have "∀x∈A. ∃y∈B. b`(y) = x"
    proof -
      { fix x assume "x∈A"
        let ?y = "a`(x)"
        from A1 A3 ‹x∈A› have "?y∈B" and "b`(?y) = x" 
          using bij_def inj_def apply_funtype by auto
        hence "∃y∈B. b`(y) = x" by auto
      } thus ?thesis by simp 
    qed
    with A2 show "b ∈ surj(B,A)" using surj_def by simp
  qed
  moreover have "b ∈ inj(B,A)"
  proof -
    have "∀w∈B.∀y∈B. b`(w) = b`(y) ⟶ w=y"
    proof -
      { fix w y assume "w∈B"  "y∈B" and I: "b`(w) = b`(y)"
        from A1 have "a ∈ surj(A,B)" unfolding bij_def by simp
        with ‹w∈B› obtain x⇩w where "x⇩w ∈ A" and II: "a`(x⇩w) = w"
          using surj_def by auto
        with I have "b`(a`(x⇩w)) = b`(y)" by simp 
        moreover from ‹a ∈ surj(A,B)› ‹y∈B› obtain x⇩y where 
          "x⇩y ∈ A" and III: "a`(x⇩y) = y"
          using surj_def by auto
        moreover from A3 ‹x⇩w ∈ A›  ‹x⇩y ∈ A› have "b`(a`(x⇩w)) = x⇩w" and  "b`(a`(x⇩y)) = x⇩y"
          by auto
        ultimately have "x⇩w = x⇩y" by simp
        with II III have "w=y" by simp 
      } thus ?thesis by auto  
    qed
    with A2 show "b ∈ inj(B,A)" using inj_def by auto
  qed
  ultimately show "b ∈ bij(B,A)" using bij_def by simp
  from assms have "b O a = id(A)" using bij_def inj_def comp_eq_id_iff1 by auto
  with A1 ‹b ∈ bij(B,A)› show "a = converse(b)" and "b = converse(a)"
    using comp_id_conv by auto
qed  
 
 
text‹For a surjection the union if images of singletons
  is the whole range.›

lemma surj_singleton_image: assumes A1: "f ∈ surj(X,Y)"
  shows "(⋃x∈X. {f`(x)}) = Y"
proof
  from A1 show "(⋃x∈X. {f`(x)}) ⊆ Y"
    using surj_def apply_funtype by auto
next 
  { fix y assume "y ∈ Y"
    with A1 have "y ∈ (⋃x∈X. {f`(x)})"
      using surj_def by auto
  } then show  "Y ⊆ (⋃x∈X. {f`(x)})" by auto
qed

subsection‹Functions of two variables›

text‹In this section we consider functions whose domain is a cartesian product
  of two sets. Such functions are called functions of two variables (although really 
  in ZF all functions admit only one argument). 
  For every function of two variables we can define families of 
  functions of one variable by fixing the other variable. This section 
  establishes basic definitions and results for this concept.›


text‹We can create functions of two variables by combining functions of one variable.›

lemma cart_prod_fun: assumes "f⇩1:X⇩1→Y⇩1"  "f⇩2:X⇩2→Y⇩2" and
  "g = {⟨p,⟨f⇩1`(fst(p)),f⇩2`(snd(p))⟩⟩. p ∈ X⇩1×X⇩2}"
  shows "g: X⇩1×X⇩2 → Y⇩1×Y⇩2" using assms apply_funtype  ZF_fun_from_total by simp

text‹A reformulation of ‹cart_prod_fun› above in a sligtly different notation.›

lemma prod_fun:
  assumes "f:X⇩1→X⇩2"  "g:X⇩3→X⇩4"
  shows "{⟨⟨x,y⟩,⟨f`x,g`y⟩⟩. ⟨x,y⟩∈X⇩1×X⇩3}:X⇩1×X⇩3→X⇩2×X⇩4" 
proof -
  have "{⟨⟨x,y⟩,⟨f`x,g`y⟩⟩. ⟨x,y⟩∈X⇩1×X⇩3} = {⟨p,⟨f`(fst(p)),g`(snd(p))⟩⟩. p ∈ X⇩1×X⇩3}"
    by auto
  with assms show ?thesis using cart_prod_fun by simp 
qed

text‹Product of two surjections is a surjection.›

theorem prod_functions_surj:
  assumes "f∈surj(A,B)" "g∈surj(C,D)"
  shows "{⟨⟨a1,a2⟩,⟨f`a1,g`a2⟩⟩.⟨a1,a2⟩∈A×C} ∈ surj(A×C,B×D)"
proof -
  let ?h = "{⟨⟨x, y⟩, f`(x), g`(y)⟩ . ⟨x,y⟩ ∈ A × C}"
  from assms have fun: "f:A→B""g:C→D" unfolding surj_def by auto
  then have pfun: "?h : A × C → B × D" using prod_fun by auto
  {
    fix b assume "b∈B×D"
    then obtain b1 b2 where "b=⟨b1,b2⟩" "b1∈B" "b2∈D" by auto
    with assms obtain a1 a2 where "f`(a1)=b1" "g`(a2)=b2" "a1∈A" "a2∈C" 
      unfolding surj_def by blast
    hence "⟨⟨a1,a2⟩,⟨b1,b2⟩⟩ ∈ ?h" by auto
    with pfun have "?h`⟨a1,a2⟩=⟨b1,b2⟩" using apply_equality by auto
    with ‹b=⟨b1,b2⟩› ‹a1∈A› ‹a2∈C› have "∃a∈A×C. ?h`(a)=b" 
      by auto
  } hence "∀b∈B×D. ∃a∈A×C. ?h`(a) = b" by auto
  with pfun show ?thesis unfolding surj_def by auto
qed


text‹For a function of two variables created from functions of one variable as in 
  ‹cart_prod_fun› above, the inverse image of a cartesian product of sets is the 
  cartesian product of inverse images.›

lemma cart_prod_fun_vimage: assumes "f⇩1:X⇩1→Y⇩1"  "f⇩2:X⇩2→Y⇩2" and
  "g = {⟨p,⟨f⇩1`(fst(p)),f⇩2`(snd(p))⟩⟩. p ∈ X⇩1×X⇩2}"
  shows "g-``(A⇩1×A⇩2) = f⇩1-``(A⇩1) × f⇩2-``(A⇩2)"
proof -
  from assms have "g: X⇩1×X⇩2 → Y⇩1×Y⇩2" using cart_prod_fun 
    by simp
  then have "g-``(A⇩1×A⇩2) = {p ∈ X⇩1×X⇩2. g`(p) ∈ A⇩1×A⇩2}" using func1_1_L15 
    by simp
  with assms ‹g: X⇩1×X⇩2 → Y⇩1×Y⇩2› show "g-``(A⇩1×A⇩2) = f⇩1-``(A⇩1) × f⇩2-``(A⇩2)" 
    using ZF_fun_from_tot_val func1_1_L15 by auto
qed
  
text‹For a function of two variables defined on $X\times Y$, if we fix an 
  $x\in X$ we obtain a function on $Y$.
  Note that if ‹domain(f)› is $X\times Y$, ‹range(domain(f))› 
  extracts $Y$ from $X\times Y$.›

definition
  "Fix1stVar(f,x) ≡ {⟨y,f`⟨x,y⟩⟩. y ∈ range(domain(f))}"
  
text‹For every $y\in Y$ we can fix the second variable in a binary function
  $f: X\times Y \rightarrow Z$ to get a function on $X$.›

definition
  "Fix2ndVar(f,y) ≡ {⟨x,f`⟨x,y⟩⟩. x ∈ domain(domain(f))}"

text‹We defined ‹Fix1stVar› and ‹Fix2ndVar› so that
  the domain of the function is not listed in the arguments, but is recovered 
  from the function. The next lemma is a technical fact that makes it easier
  to use this definition.›

lemma fix_var_fun_domain: assumes A1: "f : X×Y → Z"
  shows
  "x∈X ⟶ Fix1stVar(f,x) = {⟨y,f`⟨x,y⟩⟩. y ∈ Y}"
  "y∈Y ⟶ Fix2ndVar(f,y) = {⟨x,f`⟨x,y⟩⟩. x ∈ X}"
proof -
  from A1 have I: "domain(f) = X×Y" using func1_1_L1 by simp
  { assume "x∈X"
    with I have "range(domain(f)) = Y" by auto
    then have "Fix1stVar(f,x) = {⟨y,f`⟨x,y⟩⟩. y ∈ Y}"
      using Fix1stVar_def by simp
  } then show "x∈X ⟶ Fix1stVar(f,x) = {⟨y,f`⟨x,y⟩⟩. y ∈ Y}"
    by simp
  { assume "y∈Y"
    with I have "domain(domain(f)) = X" by auto
    then have "Fix2ndVar(f,y) = {⟨x,f`⟨x,y⟩⟩. x ∈ X}"
      using Fix2ndVar_def by simp
  } then show "y∈Y ⟶ Fix2ndVar(f,y) = {⟨x,f`⟨x,y⟩⟩. x ∈ X}"
    by simp
qed
    
text‹If we fix the first variable, we get a function of the second variable.›

lemma fix_1st_var_fun: assumes A1: "f : X×Y → Z" and A2: "x∈X"
  shows "Fix1stVar(f,x) : Y → Z"
proof -
  from A1 A2 have "∀y∈Y. f`⟨x,y⟩ ∈ Z"
    using apply_funtype by simp
  then have "{⟨y,f`⟨x,y⟩⟩. y ∈ Y} :  Y → Z" using ZF_fun_from_total by simp
  with A1 A2 show "Fix1stVar(f,x) : Y → Z" using fix_var_fun_domain by simp
qed

text‹If we fix the second variable, we get a function of the first
  variable.›

lemma fix_2nd_var_fun: assumes A1: "f : X×Y → Z" and A2: "y∈Y"
  shows "Fix2ndVar(f,y) : X → Z"
proof -
  from A1 A2 have "∀x∈X. f`⟨x,y⟩ ∈ Z"
    using apply_funtype by simp
  then have "{⟨x,f`⟨x,y⟩⟩. x ∈ X} :  X → Z"
    using ZF_fun_from_total by simp
  with A1 A2 show "Fix2ndVar(f,y) : X → Z"
    using fix_var_fun_domain by simp 
qed

text‹What is the value of ‹Fix1stVar(f,x)› at $y\in Y$
  and the value of ‹Fix2ndVar(f,y)› at $x\in X$"?›

lemma fix_var_val: 
  assumes A1: "f : X×Y → Z" and A2: "x∈X"  "y∈Y"
  shows 
  "Fix1stVar(f,x)`(y) = f`⟨x,y⟩"
  "Fix2ndVar(f,y)`(x) = f`⟨x,y⟩"
proof -
  let ?f⇩1 = "{⟨y,f`⟨x,y⟩⟩. y ∈ Y}"
  let ?f⇩2 = "{⟨x,f`⟨x,y⟩⟩. x ∈ X}"
  from A1 A2 have I:
    "Fix1stVar(f,x) = ?f⇩1"
    "Fix2ndVar(f,y) = ?f⇩2"
    using fix_var_fun_domain by auto
  moreover from A1 A2 have
    "Fix1stVar(f,x) : Y → Z"
    "Fix2ndVar(f,y) : X → Z"
    using fix_1st_var_fun fix_2nd_var_fun by auto
  ultimately have "?f⇩1 : Y → Z" and  "?f⇩2 : X → Z"
    by auto
  with A2 have "?f⇩1`(y) = f`⟨x,y⟩" and "?f⇩2`(x) = f`⟨x,y⟩"
    using ZF_fun_from_tot_val by auto
  with I show
    "Fix1stVar(f,x)`(y) = f`⟨x,y⟩"
    "Fix2ndVar(f,y)`(x) = f`⟨x,y⟩"
    by auto
qed

text‹Fixing the second variable commutes with restrictig the domain.›

lemma fix_2nd_var_restr_comm: 
  assumes A1: "f : X×Y → Z" and A2: "y∈Y" and A3: "X⇩1 ⊆ X"
  shows "Fix2ndVar(restrict(f,X⇩1×Y),y) = restrict(Fix2ndVar(f,y),X⇩1)"
proof -
  let ?g = "Fix2ndVar(restrict(f,X⇩1×Y),y)"
  let ?h = "restrict(Fix2ndVar(f,y),X⇩1)"
  from A3 have I: "X⇩1×Y ⊆ X×Y" by auto
  with A1 have II: "restrict(f,X⇩1×Y) : X⇩1×Y → Z"
    using restrict_type2 by simp
  with A2 have "?g : X⇩1 → Z"
    using fix_2nd_var_fun by simp
  moreover
  from A1 A2 have III: "Fix2ndVar(f,y) : X → Z"
    using fix_2nd_var_fun by simp
  with A3 have "?h : X⇩1 → Z"
    using restrict_type2 by simp
  moreover
  { fix z assume A4: "z ∈ X⇩1"
    with A2 I II have "?g`(z) = f`⟨z,y⟩"
      using restrict fix_var_val by simp
    also from A1 A2 A3 A4 have "f`⟨z,y⟩ = ?h`(z)"
      using restrict fix_var_val by auto
    finally have "?g`(z) = ?h`(z)" by simp
  } then have "∀z ∈ X⇩1. ?g`(z) = ?h`(z)" by simp
  ultimately show "?g = ?h" by (rule func_eq)
qed

text‹The next lemma expresses the inverse image of a set by function with fixed 
first variable in terms of the original function.›

lemma fix_1st_var_vimage:
  assumes A1: "f : X×Y → Z" and A2: "x∈X" 
  shows "Fix1stVar(f,x)-``(A) = {y∈Y. ⟨x,y⟩ ∈ f-``(A)}"
proof -
  from assms have "Fix1stVar(f,x)-``(A) = {y∈Y. Fix1stVar(f,x)`(y) ∈ A}"
    using fix_1st_var_fun func1_1_L15 by blast
  with assms show ?thesis using fix_var_val func1_1_L15 by auto
qed

text‹The next lemma expresses the inverse image of a set by function with fixed 
second variable in terms of the original function.›

lemma fix_2nd_var_vimage:
  assumes A1: "f : X×Y → Z" and A2: "y∈Y" 
  shows "Fix2ndVar(f,y)-``(A) = {x∈X. ⟨x,y⟩ ∈ f-``(A)}"
proof -
  from assms have I: "Fix2ndVar(f,y)-``(A) = {x∈X. Fix2ndVar(f,y)`(x) ∈ A}"
    using fix_2nd_var_fun func1_1_L15 by blast
  with assms show ?thesis using fix_var_val func1_1_L15 by auto
qed

end
```

