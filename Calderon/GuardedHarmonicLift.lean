import Calderon.CompactInverseDerivativeBounds

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

variable {X Z Y P : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def harmonicLiftL (J : Z →L[ℝ] X) (B : X →L[ℝ] Y) (A : Z →L[ℝ] Y)
    (_hi : A.IsInvertible) : X →L[ℝ] X :=
  ContinuousLinearMap.id ℝ X - J.comp (A.inverse.comp B)

theorem harmonicLiftL_apply (J : Z →L[ℝ] X) (B : X →L[ℝ] Y)
    (A : Z →L[ℝ] Y) (hi : A.IsInvertible) (E : X) :
    harmonicLiftL J B A hi E = E - J (A.inverse (B E)) := rfl

theorem harmonicLiftL_kernel (J : Z →L[ℝ] X) (B : X →L[ℝ] Y)
    (A : Z →L[ℝ] Y) (hi : A.IsInvertible) (hrest : B.comp J = A) (E : X) :
    B (harmonicLiftL J B A hi E) = 0 := by
  have hc : B (J (A.inverse (B E))) = B E :=
    (congrArg (fun T : Z →L[ℝ] Y => T (A.inverse (B E))) hrest).trans
      (hi.self_apply_inverse (B E))
  rw [harmonicLiftL_apply, map_sub, hc, sub_self]

def guardedHarmonicLiftFamily (J : Z →L[ℝ] X) (A : P → Z →L[ℝ] Y)
    (B : P → X →L[ℝ] Y) (p : P) : X →L[ℝ] X := by
  classical
  exact if hi : (A p).IsInvertible then harmonicLiftL J (B p) (A p) hi else 0

theorem guardedHarmonicLiftFamily_eq (J : Z →L[ℝ] X) (A : P → Z →L[ℝ] Y)
    (B : P → X →L[ℝ] Y) (p : P) (hi : (A p).IsInvertible) :
    guardedHarmonicLiftFamily J A B p = harmonicLiftL J (B p) (A p) hi := by
  classical
  simp only [guardedHarmonicLiftFamily, dif_pos hi]

theorem guardedHarmonicLiftFamily_kernel (J : Z →L[ℝ] X)
    (A : P → Z →L[ℝ] Y) (B : P → X →L[ℝ] Y) (p : P)
    (hi : (A p).IsInvertible) (hrest : (B p).comp J = A p) (E : X) :
    B p (guardedHarmonicLiftFamily J A B p E) = 0 := by
  rw [guardedHarmonicLiftFamily_eq J A B p hi]
  exact harmonicLiftL_kernel J (B p) (A p) hi hrest E

variable [CompleteSpace Z]

theorem contDiffAt_guardedHarmonicLiftFamily (J : Z →L[ℝ] X)
    (A : P → Z →L[ℝ] Y) (hA : ContDiff ℝ ∞ A)
    (B : P → X →L[ℝ] Y) (hB : ContDiff ℝ ∞ B) (p : P)
    (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (guardedHarmonicLiftFamily J A B) p := by
  have he : ∀ᶠ t in 𝓝 p, (A t).IsInvertible :=
    hA.continuous.continuousAt.eventually hi.eventually_nhds
  have hinv : ContDiffAt ℝ ∞ (fun t => (A t).inverse) p :=
    hi.contDiffAt_map_inverse.comp p hA.contDiffAt
  have hformula : ContDiffAt ℝ ∞ (fun t =>
      ContinuousLinearMap.id ℝ X - J.comp ((A t).inverse.comp (B t))) p :=
    contDiffAt_const.sub (contDiffAt_const.clm_comp (hinv.clm_comp hB.contDiffAt))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [he] with t ht
  rw [guardedHarmonicLiftFamily_eq J A B t ht]
  all_goals rfl

theorem exists_compact_guardedHarmonicLiftFamily_jet_bound (J : Z →L[ℝ] X)
    (A : P → Z →L[ℝ] Y) (hA : ContDiff ℝ ∞ A)
    (B : P → X →L[ℝ] Y) (hB : ContDiff ℝ ∞ B)
    (q : Set P) (hq : IsCompact q) (hi : ∀ p ∈ q, (A p).IsInvertible) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ q,
      ‖iteratedFDeriv ℝ j (guardedHarmonicLiftFamily J A B) p‖ ≤ C :=
  exists_compact_iteratedFDeriv_bound _ q hq
    (fun p hp => contDiffAt_guardedHarmonicLiftFamily J A hA B hB p (hi p hp)) N

theorem contDiffAt_guardedHarmonicLiftFamily_apply (J : Z →L[ℝ] X)
    (A : P → Z →L[ℝ] Y) (hA : ContDiff ℝ ∞ A)
    (B : P → X →L[ℝ] Y) (hB : ContDiff ℝ ∞ B)
    (e : P → X) (he : ContDiff ℝ ∞ e) (p : P) (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => guardedHarmonicLiftFamily J A B t (e t)) p :=
  (contDiffAt_guardedHarmonicLiftFamily J A hA B hB p hi).clm_apply he.contDiffAt

theorem exists_compact_guardedHarmonicLiftFamily_apply_jet_bound (J : Z →L[ℝ] X)
    (A : P → Z →L[ℝ] Y) (hA : ContDiff ℝ ∞ A)
    (B : P → X →L[ℝ] Y) (hB : ContDiff ℝ ∞ B)
    (e : P → X) (he : ContDiff ℝ ∞ e)
    (q : Set P) (hq : IsCompact q) (hi : ∀ p ∈ q, (A p).IsInvertible) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ q,
      ‖iteratedFDeriv ℝ j (fun t => guardedHarmonicLiftFamily J A B t (e t)) p‖ ≤ C :=
  exists_compact_iteratedFDeriv_bound _ q hq
    (fun p hp => contDiffAt_guardedHarmonicLiftFamily_apply J A hA B hB e he p (hi p hp)) N

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
