/-
  The `PA[X]` carries for the internal two-argument Veblen function.

  `InternalEpsMonoCode` transports (EPSMONO) with surjectivity folded in, and
  `InternalEpsCover` transports (COV); both at the fixed level `a = 1`.  This file is the
  level-`a` version of both, built on `InternalVeblenSurj` and `InternalVebCover`.

  ## Three different guards, and which one goes where

  * `vebFixDef₁ (a, e)` — `NF(e) ∧ vebFixIndic a e = 1`: "`e` is a fixed point of `φ_a`".
  * `vebTowBaseDef₁ (a, e)` — `NF(e) ∧ (e = 0 ∨ vebFixIndic a e = 1)`: the *tower base* guard,
    the level-`a` analogue of `VeblenSuccStep.baseDef₁`.  The cover needs `0` as well, because
    the cover of `x = 0` has no fixed point below it.
  * `vebBaseDef₁ (a, e)` — `NF(e) ∧ vebBaseIndic a e = 1`: "`e` is in the *range* of `φ_a`",
    i.e. (for `a ≠ 0`) a common fixed point of every `φ_{a'}` with `a' ≺₁ a`.  This is the one
    (EPSMONO) needs, because it is exactly the hypothesis of `InternalVeblenSurj.veb_surj'`.

  The distinction is the level-`a` form of `InternalEpsMonoCode`'s own remark that `fixDef₁`
  drops the `e = 0` disjunct of `baseDef₁`: at level `1` the three collapse to two
  (`vebBaseIndic 1 = fixIndic = vebFixIndic 0`, `InternalVeblenSurj.vebBaseIndic_one_iff`).

  ## Statements transported

  * `concrete_vebMono` — (EPSMONO) at level `a`:
    `∀a ∀e ∀g ∀u (NF(a) → Base_a(e) → NF(g) → Veb(u,a,g) → e ≺₁ u →
       ∃h (NF(h) ∧ Veb(e,a,h) ∧ h ≺₁ g))`.
  * `concrete_vebCover` — (COV_a), the successor-level cover of `InternalVebCover`:
    `∀a ∀x (NF(a) → NF(x) → ∃e ∃s ∃n ∃u (TowBase_a(e) ∧ e ≼₁ x ∧ Add(s,e,1̄) ∧
       VebTow(u,n,a,s) ∧ x ≺₁ u))`.

  The `IΣ₁` proofs are hand-written `by_cases` skeletons rather than `tauto`: the transported
  goals carry the normal-form side conditions of every graph, so the disjuncts are not
  propositionally interchangeable and `tauto` does not see the mathematical content.
-/
import OrdinalAnalysis.Gentzen.InternalVebCover

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OrdinalAnalysis.Gentzen.InternalVeblenCode

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode paLX_of_peano_semantic)
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.CodedVeblenJump
open OrdinalAnalysis.Gentzen.VNoteBridge
open OrdinalAnalysis.Gentzen.OmegaTower (lMap_numeral)
open OrdinalAnalysis.Gentzen.VeblenTower
open OrdinalAnalysis.Gentzen.VeblenSuccStep (modelCode_one)
open OrdinalAnalysis.Gentzen.InternalEpsCover (leqDef₁ leqCode₁ eval_leqDef₁)
open OrdinalAnalysis.Gentzen.InternalVeblen
open OrdinalAnalysis.Gentzen.InternalVeblenSurj
open OrdinalAnalysis.Gentzen.InternalVebCover

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The Veblen graph `Veb(y, a, g)` -/

/-- `Veb(y, a, g)`: `a` and `g` are normal codes and `y = φ_a(g)`. -/
def vebDef₁ : 𝚺₁.Semisentence 3 := .mkSigma
  “y a g. !isNFb₁Def 1 a ∧ !isNFb₁Def 1 g ∧ !iveblenDef y a g”

@[simp] theorem eval_vebDef₁ (y a g : V) :
    vebDef₁.val.Evalb ![y, a, g] ↔ isNF₁ a ∧ isNF₁ g ∧ y = iveblen a g := by
  simp [vebDef₁, isNF₁, isNFb₁_defined.iff, iveblen_defined.iff, eq_comm]

/-- The Veblen graph, in `LX`. -/
def vebCode₁ : Semiformula LX ℕ 3 := liftCode vebDef₁

/-- Apply a result-first Veblen graph: `Veb(y, a, g)`. -/
def vebAt (vebCode : Semiformula LX ℕ 3) {n : ℕ}
    (y a g : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![y, a, g] ▹ vebCode

@[simp] theorem eval_vebAt {M : Type*} [Structure LX M]
    (vebCode : Semiformula LX ℕ 3) {n : ℕ} (y a g : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    (vebAt vebCode y a g).Eval e f ↔
      vebCode.Eval ![y.val e f, a.val e f, g.val e f] f := by
  simp [vebAt]

/-! ## The three guards -/

/-- `Fix_a(e)`: `e` is a normal code and a fixed point of `φ_a`. -/
def vebFixDef₁ : 𝚺₁.Semisentence 2 := .mkSigma
  “a e. !isNFb₁Def 1 e ∧ !vebFixIndicDef 1 a e”

@[simp] theorem eval_vebFixDef₁ (a e : V) :
    vebFixDef₁.val.Evalb ![a, e] ↔ isNF₁ e ∧ vebFixIndic a e = 1 := by
  simp [vebFixDef₁, isNF₁, isNFb₁_defined.iff, vebFixIndic_defined.iff, eq_comm]

/-- The fixed-point guard, in `LX`. -/
def vebFixCode₁ : Semiformula LX ℕ 2 := liftCode vebFixDef₁

/-- `Base_a(e)`: `e` is a normal code in the *range* of `φ_a`.  This is the guard (EPSMONO)
needs — see the module docstring. -/
def vebBaseDef₁ : 𝚺₁.Semisentence 2 := .mkSigma
  “a e. !isNFb₁Def 1 e ∧ !vebBaseIndicDef 1 a e”

@[simp] theorem eval_vebBaseDef₁ (a e : V) :
    vebBaseDef₁.val.Evalb ![a, e] ↔ isNF₁ e ∧ vebBaseIndic a e = 1 := by
  simp [vebBaseDef₁, isNF₁, isNFb₁_defined.iff, vebBaseIndic_defined.iff, eq_comm]

/-- The range guard, in `LX`. -/
def vebBaseCode₁ : Semiformula LX ℕ 2 := liftCode vebBaseDef₁

/-- `TowBase_a(e)`: `e` is a normal code which is `0` or a fixed point of `φ_a` — the level-`a`
analogue of `VeblenSuccStep.baseDef₁`. -/
def vebTowBaseDef₁ : 𝚺₁.Semisentence 2 := .mkSigma
  “a e. !isNFb₁Def 1 e ∧ (e = 0 ∨ !vebFixIndicDef 1 a e)”

@[simp] theorem eval_vebTowBaseDef₁ (a e : V) :
    vebTowBaseDef₁.val.Evalb ![a, e] ↔ isNF₁ e ∧ (e = 0 ∨ vebFixIndic a e = 1) := by
  simp [vebTowBaseDef₁, isNF₁, isNFb₁_defined.iff, vebFixIndic_defined.iff, eq_comm]

/-- The tower-base guard, in `LX`. -/
def vebTowBaseCode₁ : Semiformula LX ℕ 2 := liftCode vebTowBaseDef₁

/-! ## The Veblen-tower graph `VebTow(u, n, a, c)` -/

/-- `VebTow(u, k, a, c)`: `a` and `c` are normal codes and `u` is the `k`-th `φ_a`-tower stage
over `c`.  The level-`a` analogue of `VeblenTower.towerDef₁`. -/
def vebTowDef₁ : 𝚺₁.Semisentence 4 := .mkSigma
  “u k a c. !isNFb₁Def 1 a ∧ !isNFb₁Def 1 c ∧ !ivebTowerDef u a c k”

@[simp] theorem eval_vebTowDef₁ (u k a c : V) :
    vebTowDef₁.val.Evalb ![u, k, a, c] ↔ isNF₁ a ∧ isNF₁ c ∧ u = ivebTower a c k := by
  simp [vebTowDef₁, isNF₁, isNFb₁_defined.iff, ivebTower_defined.iff, eq_comm]

/-- The Veblen-tower graph, in `LX`. -/
def vebTowCode₁ : Semiformula LX ℕ 4 := liftCode vebTowDef₁

/-- Apply a result-first four-place Veblen-tower graph: `VebTow(u, k, a, c)`. -/
def vebTowAt (towCode : Semiformula LX ℕ 4) {n : ℕ}
    (u k a c : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![u, k, a, c] ▹ towCode

@[simp] theorem eval_vebTowAt {M : Type*} [Structure LX M]
    (towCode : Semiformula LX ℕ 4) {n : ℕ} (u k a c : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    (vebTowAt towCode u k a c).Eval e f ↔
      towCode.Eval ![u.val e f, k.val e f, a.val e f, c.val e f] f := by
  simp [vebTowAt]

/-! ## The statements -/

/--
**(EPSMONO) at level `a`, with surjectivity folded in.**

`∀a ∀e ∀g ∀u (NF(a) → Base_a(e) → NF(g) → Veb(u,a,g) → e ≺₁ u →
  ∃h (NF(h) ∧ Veb(e,a,h) ∧ h ≺₁ g))`.
-/
noncomputable def vebMonoStatement : Sentence LX :=
  (∀¹ ∀¹ ∀¹ ∀¹
    (∼(formulaAt nfCode₁ (#3 : Semiterm LX ℕ 4)) ⋎
      (∼(precAt vebBaseCode₁ #3 #2) ⋎
        (∼(formulaAt nfCode₁ (#1 : Semiterm LX ℕ 4)) ⋎
          (∼(vebAt vebCode₁ (#0 : Semiterm LX ℕ 4) #3 #1) ⋎
            (∼(precAt precCode₁ #2 #0) ⋎
              (∃¹
                (formulaAt nfCode₁ (#0 : Semiterm LX ℕ 5) ⋏
                  (vebAt vebCode₁ (#3 : Semiterm LX ℕ 5) #4 #0 ⋏
                    precAt precCode₁ #0 #2))))))))).univCl

/--
**(COV_a), in the object language.**

`∀a ∀x (NF(a) → NF(x) → ∃e ∃s ∃n ∃u (TowBase_a(e) ∧ e ≼₁ x ∧ Add(s,e,1̄) ∧
  VebTow(u,n,a,s) ∧ x ≺₁ u))`.
-/
noncomputable def vebCoverStatement : Sentence LX :=
  (∀¹ ∀¹
    (∼(formulaAt nfCode₁ (#1 : Semiterm LX ℕ 2)) ⋎
      (∼(formulaAt nfCode₁ (#0 : Semiterm LX ℕ 2)) ⋎
        (∃¹ ∃¹ ∃¹ ∃¹
          (precAt vebTowBaseCode₁ #5 #3 ⋏
            (precAt leqCode₁ #3 #4 ⋏
              (addAt addCode₁ #2 #3 ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 6) ⋏
                (vebTowAt vebTowCode₁ #0 #1 #5 #2 ⋏
                  precAt precCode₁ #4 #0)))))))).univCl

private def arithNfAt {n : ℕ} (x : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x] ▹ Rewriting.emb nfDef₁.val

private def arithPrecAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb precDef₁.val

private def arithLeqAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb leqDef₁.val

private def arithVebBaseAt {n : ℕ} (a e : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![a, e] ▹ Rewriting.emb vebBaseDef₁.val

private def arithVebTowBaseAt {n : ℕ} (a e : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![a, e] ▹ Rewriting.emb vebTowBaseDef₁.val

private def arithVebAt {n : ℕ} (y a g : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![y, a, g] ▹ Rewriting.emb vebDef₁.val

private def arithAddAt {n : ℕ} (z x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, x, y] ▹ Rewriting.emb safeIadd₁Def.val

private def arithVebTowAt {n : ℕ}
    (u k a c : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![u, k, a, c] ▹ Rewriting.emb vebTowDef₁.val

noncomputable def arithmeticVebMonoStatement : ArithmeticSentence :=
  (∀¹ ∀¹ ∀¹ ∀¹
    (∼(arithNfAt (#3 : Semiterm ℒₒᵣ ℕ 4)) ⋎
      (∼(arithVebBaseAt #3 #2) ⋎
        (∼(arithNfAt (#1 : Semiterm ℒₒᵣ ℕ 4)) ⋎
          (∼(arithVebAt (#0 : Semiterm ℒₒᵣ ℕ 4) #3 #1) ⋎
            (∼(arithPrecAt #2 #0) ⋎
              (∃¹
                (arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 5) ⋏
                  (arithVebAt (#3 : Semiterm ℒₒᵣ ℕ 5) #4 #0 ⋏
                    arithPrecAt #0 #2))))))))).univCl

noncomputable def arithmeticVebCoverStatement : ArithmeticSentence :=
  (∀¹ ∀¹
    (∼(arithNfAt (#1 : Semiterm ℒₒᵣ ℕ 2)) ⋎
      (∼(arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 2)) ⋎
        (∃¹ ∃¹ ∃¹ ∃¹
          (arithVebTowBaseAt #5 #3 ⋏
            (arithLeqAt #3 #4 ⋏
              (arithAddAt #2 #3 ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 6) ⋏
                (arithVebTowAt #0 #1 #5 #2 ⋏
                  arithPrecAt #4 #0)))))))).univCl

/-! ## The `IΣ₁` proofs -/

theorem arithmetic_vebMono : 𝗜𝚺₁ ⊢ arithmeticVebMonoStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticVebMonoStatement, arithNfAt, arithVebBaseAt, arithVebAt, arithPrecAt,
    eval_vebBaseDef₁, eval_nfDef₁, eval_precDef₁, eval_vebDef₁]
  intro a e g u
  by_cases hna : isNF₁ a
  · right
    by_cases hbe : isNF₁ e ∧ vebBaseIndic a e = 1
    · obtain ⟨hne, hbase⟩ := hbe
      right
      by_cases hng : isNF₁ g
      · right
        by_cases hu : u = iveblen a g
        · right
          by_cases hlt : icmp₁ e u = 0
          · right
            obtain ⟨h, hh, hhe, hhg⟩ := veb_mono_of_surj hna hne hbase hng hu hlt
            exact ⟨h, hh, ⟨hna, hh, hhe⟩, hh, hng, hhg⟩
          · left
            intro _ _
            exact hlt
        · left
          intro _ _
          exact hu
      · left
        exact hng
    · left
      intro hne hbase
      exact hbe ⟨hne, hbase⟩
  · left
    exact hna

theorem arithmetic_vebCover : 𝗜𝚺₁ ⊢ arithmeticVebCoverStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticVebCoverStatement, arithNfAt, arithVebTowBaseAt, arithPrecAt, arithLeqAt,
    arithAddAt, arithVebTowAt, eval_nfDef₁, eval_vebTowBaseDef₁, eval_precDef₁, eval_leqDef₁,
    eval_vebTowDef₁, safeIadd₁_defined.iff,
    Structure.numeral_eq_numeral, numeral_eq_natCast]
  intro a x
  by_cases hna : isNF₁ a
  · right
    by_cases hx : isNF₁ x
    · right
      have hone : ((gamma0Code 1 : ℕ) : M) = vcVadd 0 0 1 0 := modelCode_one
      obtain ⟨e, n, he, hbase, hle, hcov⟩ := veb_cover_aux a hna x hx
      refine ⟨e, ?_⟩
      rw [hone, safeIadd₁_of_nf he]
      exact ⟨⟨he, hbase⟩, ⟨he, hx, hle⟩, ⟨hna, isNF₁_vebSuccBase he hbase⟩, hx, n,
        isNF₁_ivebTower hna (isNF₁_vebSuccBase he hbase) n, hcov⟩
    · left
      exact hx
  · left
    exact hna

/-! ## Transport to `PA[X]` -/

private lemma map_vebMono_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹ ∀¹
          (∼(arithNfAt (#3 : Semiterm ℒₒᵣ ℕ 4)) ⋎
            (∼(arithVebBaseAt #3 #2) ⋎
              (∼(arithNfAt (#1 : Semiterm ℒₒᵣ ℕ 4)) ⋎
                (∼(arithVebAt (#0 : Semiterm ℒₒᵣ ℕ 4) #3 #1) ⋎
                  (∼(arithPrecAt #2 #0) ⋎
                    (∃¹
                      (arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 5) ⋏
                        (arithVebAt (#3 : Semiterm ℒₒᵣ ℕ 5) #4 #0 ⋏
                          arithPrecAt #0 #2))))))))) =
      (∀¹ ∀¹ ∀¹ ∀¹
        (∼(formulaAt nfCode₁ (#3 : Semiterm LX ℕ 4)) ⋎
          (∼(precAt vebBaseCode₁ #3 #2) ⋎
            (∼(formulaAt nfCode₁ (#1 : Semiterm LX ℕ 4)) ⋎
              (∼(vebAt vebCode₁ (#0 : Semiterm LX ℕ 4) #3 #1) ⋎
                (∼(precAt precCode₁ #2 #0) ⋎
                  (∃¹
                    (formulaAt nfCode₁ (#0 : Semiterm LX ℕ 5) ⋏
                      (vebAt vebCode₁ (#3 : Semiterm LX ℕ 5) #4 #0 ⋏
                        precAt precCode₁ #0 #2))))))))) := by
  simp [arithNfAt, arithVebBaseAt, arithVebAt, arithPrecAt, formulaAt, precAt, vebAt,
    nfCode₁, vebBaseCode₁, vebCode₁, precCode₁, liftCode, Semiformula.lMap_subst]

private lemma map_vebCover_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹
          (∼(arithNfAt (#1 : Semiterm ℒₒᵣ ℕ 2)) ⋎
            (∼(arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 2)) ⋎
              (∃¹ ∃¹ ∃¹ ∃¹
                (arithVebTowBaseAt #5 #3 ⋏
                  (arithLeqAt #3 #4 ⋏
                    (arithAddAt #2 #3 ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 6) ⋏
                      (arithVebTowAt #0 #1 #5 #2 ⋏
                        arithPrecAt #4 #0)))))))) =
      (∀¹ ∀¹
        (∼(formulaAt nfCode₁ (#1 : Semiterm LX ℕ 2)) ⋎
          (∼(formulaAt nfCode₁ (#0 : Semiterm LX ℕ 2)) ⋎
            (∃¹ ∃¹ ∃¹ ∃¹
              (precAt vebTowBaseCode₁ #5 #3 ⋏
                (precAt leqCode₁ #3 #4 ⋏
                  (addAt addCode₁ #2 #3 ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 6) ⋏
                    (vebTowAt vebTowCode₁ #0 #1 #5 #2 ⋏
                      precAt precCode₁ #4 #0)))))))) := by
  simp [arithNfAt, arithVebTowBaseAt, arithPrecAt, arithLeqAt, arithAddAt, arithVebTowAt,
    formulaAt, precAt, addAt, vebTowAt, nfCode₁, vebTowBaseCode₁, precCode₁, leqCode₁,
    addCode₁, vebTowCode₁, liftCode, Semiformula.lMap_subst, lMap_numeral]

lemma models_vebMono_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ vebMonoStatement ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticVebMonoStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [vebMonoStatement, arithmeticVebMonoStatement, Semiformula.eval_univCl]
  rw [← map_vebMono_body]
  simp [Semiformula.eval_lMap]

lemma models_vebCover_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ vebCoverStatement ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticVebCoverStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [vebCoverStatement, arithmeticVebCoverStatement, Semiformula.eval_univCl]
  rw [← map_vebCover_body]
  simp [Semiformula.eval_lMap]

/-- **(EPSMONO) at level `a`, with surjectivity folded in, in `PA[X]`.** -/
theorem concrete_vebMono : paLX ⊢ vebMonoStatement := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_vebMono)
  intro M _ _
  exact models_vebMono_iff_arithmetic

/-- **(COV_a), in `PA[X]`.** -/
theorem concrete_vebCover : paLX ⊢ vebCoverStatement := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_vebCover)
  intro M _ _
  exact models_vebCover_iff_arithmetic

/-! ## Semantic form, for the second-order layer -/

theorem models_vebMonoStatement {M : Type*} [Nonempty M] [Structure LX M]
    [Structure.Eq LX M] :
    M↓[LX] ⊧ vebMonoStatement ↔
      ∀ f : ℕ → M, ∀ a e g u : M,
        nfCode₁.Eval ![a] f →
        vebBaseCode₁.Eval ![a, e] f →
        nfCode₁.Eval ![g] f →
        vebCode₁.Eval ![u, a, g] f →
        precCode₁.Eval ![e, u] f →
        ∃ h : M, nfCode₁.Eval ![h] f ∧ vebCode₁.Eval ![e, a, h] f ∧
          precCode₁.Eval ![h, g] f := by
  classical
  simp [models_iff, vebMonoStatement]
  constructor
  · intro h f a e g u hna hb hng hv hp
    rcases h f a e g u with hn1 | hn2 | hn3 | hn4 | hn5 | hgoal
    · exact (hn1 hna).elim
    · exact (hn2 hb).elim
    · exact (hn3 hng).elim
    · exact (hn4 hv).elim
    · exact (hn5 hp).elim
    · exact hgoal
  · intro h f a e g u
    by_cases hna : nfCode₁.Eval ![a] f
    · right
      by_cases hb : vebBaseCode₁.Eval ![a, e] f
      · right
        by_cases hng : nfCode₁.Eval ![g] f
        · right
          by_cases hv : vebCode₁.Eval ![u, a, g] f
          · right
            by_cases hp : precCode₁.Eval ![e, u] f
            · exact Or.inr (h f a e g u hna hb hng hv hp)
            · exact Or.inl hp
          · exact Or.inl hv
        · exact Or.inl hng
      · exact Or.inl hb
    · exact Or.inl hna

end OrdinalAnalysis.Gentzen.InternalVeblenCode
