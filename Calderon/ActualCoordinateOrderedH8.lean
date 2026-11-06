import Calderon.CoordinateBootstrapJets
import Calderon.PrincipalDirectional
import Calderon.ReferenceRadiusScaling
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Count

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualCoordinateOrderedH8
open CoordinateBootstrapJets PrincipalCommutator ConformalDepth RadiusProfile ReferenceDensityBounds

def SmoothScalarField : Type := {f : R3 → ℝ // ContDiff ℝ ∞ f}

def smoothCoordinateDerivative (k : Fin 3) (F : SmoothScalarField) : SmoothScalarField :=
  ⟨coordinateDerivative k F.1,contDiff_directionalFDeriv (coordinateDirection k) F.1 F.2⟩

lemma smoothCoordinateDerivative_commute (k l : Fin 3) :
    Function.Commute (smoothCoordinateDerivative k) (smoothCoordinateDerivative l) := by
  intro F
  apply Subtype.ext
  funext x
  exact directionalFDeriv_commute (coordinateDirection k) (coordinateDirection l) F.1 F.2 x

lemma smoothCoordinateDerivative_iterate_coe (k : Fin 3) (n : ℕ) (F : SmoothScalarField) :
    (((smoothCoordinateDerivative k)^[n]) F).1 = ((coordinateDerivative k)^[n]) F.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change coordinateDerivative k (((smoothCoordinateDerivative k)^[n]) F).1 =
      coordinateDerivative k (((coordinateDerivative k)^[n]) F.1)
    rw [ih]

def coordinateWordPartial : List (Fin 3) → (R3 → ℝ) → R3 → ℝ
  | [],f => f
  | k::w,f => coordinateDerivative k (coordinateWordPartial w f)

lemma contDiff_coordinateWordPartial (w : List (Fin 3))
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordinateWordPartial w f) := by
  induction w with
  | nil => exact hf
  | cons k w ih =>
    exact contDiff_directionalFDeriv (coordinateDirection k) (coordinateWordPartial w f) ih

lemma smoothCoordinateWord_coe (w : List (Fin 3)) (F : SmoothScalarField) :
    (w.foldr smoothCoordinateDerivative F).1 = coordinateWordPartial w F.1 := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change coordinateDerivative k (w.foldr smoothCoordinateDerivative F).1 =
      coordinateDerivative k (coordinateWordPartial w F.1)
    rw [ih]

theorem smoothCoordinateWord_eq_count_iterates (w : List (Fin 3)) (F : SmoothScalarField) :
    w.foldr smoothCoordinateDerivative F =
      ((smoothCoordinateDerivative 0)^[w.count 0])
        (((smoothCoordinateDerivative 1)^[w.count 1])
          (((smoothCoordinateDerivative 2)^[w.count 2]) F)) := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    rw [List.foldr_cons, ih]
    fin_cases k
    · simp [List.count_cons, Function.iterate_succ_apply']
    · have h10 := (smoothCoordinateDerivative_commute 1 0).iterate_right (w.count 0)
      simpa [List.count_cons, Function.iterate_succ_apply'] using
        h10.eq (((smoothCoordinateDerivative 1)^[w.count 1])
          (((smoothCoordinateDerivative 2)^[w.count 2]) F))
    · have h20 := (smoothCoordinateDerivative_commute 2 0).iterate_right (w.count 0)
      have h21 := (smoothCoordinateDerivative_commute 2 1).iterate_right (w.count 1)
      calc
        smoothCoordinateDerivative 2
            (((smoothCoordinateDerivative 0)^[w.count 0])
              (((smoothCoordinateDerivative 1)^[w.count 1])
                (((smoothCoordinateDerivative 2)^[w.count 2]) F))) =
            ((smoothCoordinateDerivative 0)^[w.count 0])
              (smoothCoordinateDerivative 2
                (((smoothCoordinateDerivative 1)^[w.count 1])
                  (((smoothCoordinateDerivative 2)^[w.count 2]) F))) := h20.eq _
        _ = ((smoothCoordinateDerivative 0)^[w.count 0])
              (((smoothCoordinateDerivative 1)^[w.count 1])
                (smoothCoordinateDerivative 2
                  (((smoothCoordinateDerivative 2)^[w.count 2]) F))) :=
          congrArg ((smoothCoordinateDerivative 0)^[w.count 0]) (h21.eq _)
        _ = ((smoothCoordinateDerivative 0)^[(2::w).count 0])
              (((smoothCoordinateDerivative 1)^[(2::w).count 1])
                (((smoothCoordinateDerivative 2)^[(2::w).count 2]) F)) := by
          simp [List.count_cons, Function.iterate_succ_apply']

lemma coordinateWordPartial_eq_count_iterates (w : List (Fin 3))
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    coordinateWordPartial w f =
      ((coordinateDerivative 0)^[w.count 0])
        (((coordinateDerivative 1)^[w.count 1]) (((coordinateDerivative 2)^[w.count 2]) f)) := by
  let F : SmoothScalarField := ⟨f,hf⟩
  let F2 : SmoothScalarField := ((smoothCoordinateDerivative 2)^[w.count 2]) F
  let F1 : SmoothScalarField := ((smoothCoordinateDerivative 1)^[w.count 1]) F2
  have he : (w.foldr smoothCoordinateDerivative F).1 =
      (((smoothCoordinateDerivative 0)^[w.count 0]) F1).1 :=
    congrArg (fun V : SmoothScalarField => V.1) (smoothCoordinateWord_eq_count_iterates w F)
  calc
    coordinateWordPartial w f = (w.foldr smoothCoordinateDerivative F).1 :=
      (smoothCoordinateWord_coe w F).symm
    _ = (((smoothCoordinateDerivative 0)^[w.count 0]) F1).1 := he
    _ = ((coordinateDerivative 0)^[w.count 0]) F1.1 :=
      smoothCoordinateDerivative_iterate_coe 0 (w.count 0) F1
    _ = ((coordinateDerivative 0)^[w.count 0])
        (((coordinateDerivative 1)^[w.count 1]) F2.1) :=
      congrArg ((coordinateDerivative 0)^[w.count 0])
        (smoothCoordinateDerivative_iterate_coe 1 (w.count 1) F2)
    _ = ((coordinateDerivative 0)^[w.count 0])
        (((coordinateDerivative 1)^[w.count 1]) (((coordinateDerivative 2)^[w.count 2]) f)) :=
      congrArg (fun v => ((coordinateDerivative 0)^[w.count 0])
        (((coordinateDerivative 1)^[w.count 1]) v))
        (smoothCoordinateDerivative_iterate_coe 2 (w.count 2) F)

lemma coordinateWord_count_sum (w : List (Fin 3)) :
    (∑ k : Fin 3, w.count k) = w.length := by
  induction w with
  | nil => simp
  | cons k w ih =>
    fin_cases k <;> simp [List.count_cons, Fin.sum_univ_three, List.length_cons] at * <;> omega

def coordinateWordMultiIndex (w : List (Fin 3)) (hw : w.length ≤ 8) : Fin 3 → Fin 9 :=
  fun k => ⟨w.count k,by have hc : w.count k ≤ w.length := List.count_le_length; omega⟩

lemma multiIndexOrder_coordinateWordMultiIndex (w : List (Fin 3)) (hw : w.length ≤ 8) :
    multiIndexOrder (coordinateWordMultiIndex w hw) = w.length := by
  change (∑ k : Fin 3, w.count k) = w.length
  exact coordinateWord_count_sum w

theorem coordinateWordPartial_eq_canonicalCoordinatePartial
    (w : List (Fin 3)) (hw : w.length ≤ 8)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    coordinateWordPartial w f = canonicalCoordinatePartial (coordinateWordMultiIndex w hw) f := by
  rw [coordinateWordPartial_eq_count_iterates w f hf]
  rfl

theorem abs_coordinateWordPartial_component_le_H8
    (w : List (Fin 3)) (hw : w.length ≤ 8) (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (x : R3) (i j : Fin 3) :
    |coordinateWordPartial w (fun y => h y i j) x| ≤ coordinateH8 h x := by
  rw [coordinateWordPartial_eq_canonicalCoordinatePartial w hw _ (hh i j)]
  exact abs_component_partial_le_H8 (coordinateWordMultiIndex w hw) h x
    (by rw [multiIndexOrder_coordinateWordMultiIndex]; exact hw) i j

theorem abs_coordinateWordPartial_component_le_of_H8
    (w : List (Fin 3)) (hw : w.length ≤ 8) (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (x : R3) (i j : Fin 3)
    (A : ℝ) (hA : coordinateH8 h x ≤ A) :
    |coordinateWordPartial w (fun y => h y i j) x| ≤ A := by
  exact (abs_coordinateWordPartial_component_le_H8 w hw h hh x i j).trans hA

theorem abs_coordinateWordPartial_component_weighted_of_H8
    (w : List (Fin 3)) (hw : w.length ≤ 8) (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (x : R3) (i j : Fin 3)
    (eps beta δ R L : ℝ) (p : ℕ) (heps : 0 ≤ eps) (hb : 1 ≤ beta)
    (hδ : 0 < δ) (hR : 0 < R) (hH8 : coordinateH8 h x ≤ eps*referenceRadius δ R p L x) :
    |coordinateWordPartial w (fun y => h y i j) x| ≤
      eps*referenceRadius δ R p L x*beta^w.length := by
  have hr := referenceRadius_pos δ R p L x hδ hR
  have hp : 1 ≤ beta^w.length := one_le_pow₀ hb
  have he : 0 ≤ eps*referenceRadius δ R p L x := mul_nonneg heps hr.le
  calc
    |coordinateWordPartial w (fun y => h y i j) x| ≤
        eps*referenceRadius δ R p L x :=
      abs_coordinateWordPartial_component_le_of_H8 w hw h hh x i j _ hH8
    _ ≤ eps*referenceRadius δ R p L x*beta^w.length := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp he

end OAI.AnisotropicCalderon.ActualCoordinateOrderedH8
