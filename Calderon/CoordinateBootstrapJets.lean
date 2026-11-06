import Calderon.PerturbedDensityAdjoint
import Mathlib.Analysis.Normed.Lp.PiLp

set_option autoImplicit false
noncomputable section
open scoped ContDiff
open WithLp
namespace OAI.AnisotropicCalderon.CoordinateBootstrapJets
open PrincipalCommutator PerturbedDensityAdjoint ReferenceDensityBounds

/-- The actual coordinate derivative, acting on scalar functions. -/
def coordinateDerivative (k : Fin 3) (f : R3 → ℝ) : R3 → ℝ :=
  directionalFDeriv (coordinateDirection k) f

def multiIndexOrder (alpha : Fin 3 → Fin 9) : ℕ := ∑ k, (alpha k).val

/-- Fixed coordinate order for a literal multiindex, with no Frechet operator norm. -/
def canonicalCoordinatePartial (alpha : Fin 3 → Fin 9) (f : R3 → ℝ) : R3 → ℝ :=
  ((coordinateDerivative 0)^[ (alpha 0).val ])
    (((coordinateDerivative 1)^[ (alpha 1).val ])
      (((coordinateDerivative 2)^[ (alpha 2).val ]) f))

/-- The nine coordinate tensor entries with the explicit Euclidean norm. -/
def coordinateTensorPartial (alpha : Fin 3 → Fin 9) (h : MatrixField) (x : R3) :
    EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  toLp 2 (fun ij => canonicalCoordinatePartial alpha (fun y => h y ij.1 ij.2) x)

/-- Each permitted three-dimensional multiindex occurs exactly once. -/
def coordinateH8 (h : MatrixField) (x : R3) : ℝ :=
  ∑ alpha : Fin 3 → Fin 9,
    if multiIndexOrder alpha ≤ 8 then ‖coordinateTensorPartial alpha h x‖ else 0

def zeroMultiIndex : Fin 3 → Fin 9 := fun _ => 0
def firstMultiIndex (k : Fin 3) : Fin 3 → Fin 9 := fun j => if j=k then 1 else 0
def secondMultiIndex (k l : Fin 3) : Fin 3 → Fin 9 :=
  fun j => firstMultiIndex k j + firstMultiIndex l j

lemma multiIndexOrder_zero : multiIndexOrder zeroMultiIndex = 0 := by
  simp [multiIndexOrder,zeroMultiIndex]

lemma multiIndexOrder_first (k : Fin 3) : multiIndexOrder (firstMultiIndex k) = 1 := by
  fin_cases k <;> norm_num [multiIndexOrder,firstMultiIndex,Fin.sum_univ_three]

lemma multiIndexOrder_second (k l : Fin 3) : multiIndexOrder (secondMultiIndex k l) = 2 := by
  fin_cases k <;> fin_cases l <;>
    norm_num [multiIndexOrder,secondMultiIndex,firstMultiIndex,Fin.sum_univ_three]

lemma canonicalCoordinatePartial_zero (f : R3 → ℝ) :
    canonicalCoordinatePartial zeroMultiIndex f = f := rfl

lemma canonicalCoordinatePartial_first (k : Fin 3) (f : R3 → ℝ) :
    canonicalCoordinatePartial (firstMultiIndex k) f =
      directionalFDeriv (coordinateDirection k) f := by
  fin_cases k <;> simp [canonicalCoordinatePartial,firstMultiIndex,coordinateDerivative]

lemma canonicalCoordinatePartial_second (k l : Fin 3) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    canonicalCoordinatePartial (secondMultiIndex k l) f =
      directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) f) := by
  funext x
  fin_cases k <;> fin_cases l <;>
    simp [canonicalCoordinatePartial,secondMultiIndex,firstMultiIndex,coordinateDerivative] <;>
    first | rfl | exact directionalFDeriv_commute _ _ f hf x

lemma coordinateH8_nonneg (h : MatrixField) (x : R3) : 0 ≤ coordinateH8 h x := by
  apply Finset.sum_nonneg
  intro alpha ha
  split_ifs <;> positivity

lemma norm_coordinateTensorPartial_le_H8 (alpha : Fin 3 → Fin 9)
    (h : MatrixField) (x : R3) (ha : multiIndexOrder alpha ≤ 8) :
    ‖coordinateTensorPartial alpha h x‖ ≤ coordinateH8 h x := by
  have ht := Finset.single_le_sum
    (s := Finset.univ) (a := alpha)
    (f := fun a : Fin 3 → Fin 9 =>
      if multiIndexOrder a ≤ 8 then ‖coordinateTensorPartial a h x‖ else 0)
    (fun a _ => by split_ifs <;> positivity) (Finset.mem_univ alpha)
  simpa only [if_pos ha,coordinateH8] using ht

lemma abs_component_partial_le_H8 (alpha : Fin 3 → Fin 9)
    (h : MatrixField) (x : R3) (ha : multiIndexOrder alpha ≤ 8) (i j : Fin 3) :
    |canonicalCoordinatePartial alpha (fun y => h y i j) x| ≤ coordinateH8 h x := by
  have ht := PiLp.norm_apply_le (coordinateTensorPartial alpha h x) (i,j)
  have hn : |canonicalCoordinatePartial alpha (fun y => h y i j) x| ≤
      ‖coordinateTensorPartial alpha h x‖ := by
    simpa only [Real.norm_eq_abs,coordinateTensorPartial,WithLp.ofLp_toLp] using ht
  exact hn.trans (norm_coordinateTensorPartial_le_H8 alpha h x ha)

/-- The source bootstrap controls each literal scalar two-jet. -/
lemma twoJetBound_component_of_coordinateH8 (h : MatrixField) (x : R3)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (i j k l : Fin 3) :
    TwoJetBound (coordinateDirection k) (coordinateDirection l)
      (fun y => h y i j) x (coordinateH8 h x) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [canonicalCoordinatePartial_zero] using
      abs_component_partial_le_H8 zeroMultiIndex h x (by rw [multiIndexOrder_zero]; norm_num) i j
  · simpa only [canonicalCoordinatePartial_first] using
      abs_component_partial_le_H8 (firstMultiIndex k) h x
        (by rw [multiIndexOrder_first]; norm_num) i j
  · simpa only [canonicalCoordinatePartial_first] using
      abs_component_partial_le_H8 (firstMultiIndex l) h x
        (by rw [multiIndexOrder_first]; norm_num) i j
  · simpa only [canonicalCoordinatePartial_second k l _ (hh i j)] using
      abs_component_partial_le_H8 (secondMultiIndex k l) h x
        (by rw [multiIndexOrder_second]; norm_num) i j

lemma twoJetBound_component_of_coordinateH8_le (h : MatrixField) (x : R3)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (i j k l : Fin 3)
    (A : ℝ) (hA : coordinateH8 h x ≤ A) :
    TwoJetBound (coordinateDirection k) (coordinateDirection l) (fun y => h y i j) x A :=
  twoJetBound_mono _ _ _ _ _ _ (twoJetBound_component_of_coordinateH8 h x hh i j k l) hA

end OAI.AnisotropicCalderon.CoordinateBootstrapJets
