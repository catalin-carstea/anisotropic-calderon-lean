import Calderon.MetricOperator
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.NormalCoordinatesFrame
open MetricOperator

def coordinateVector (i : Fin 3) : R3 := EuclideanSpace.single i 1

def IsMetricOrthonormalFrame (M : R3 →L[ℝ] R3) (e : Fin 3 → R3) : Prop :=
  ∀ i j, inner ℝ (M (e i)) (e j) = if i = j then 1 else 0

def metricPair (M : R3 →L[ℝ] R3) (v w : R3) : ℝ := ⟪M v,w⟫_ℝ

def gramSecond (M : R3 →L[ℝ] R3) : R3 :=
  coordinateVector 1 - (metricPair M (coordinateVector 1) (coordinateVector 0) /
    metricPair M (coordinateVector 0) (coordinateVector 0)) • coordinateVector 0

def gramThird (M : R3 →L[ℝ] R3) : R3 :=
  coordinateVector 2 - (metricPair M (coordinateVector 2) (coordinateVector 0) /
    metricPair M (coordinateVector 0) (coordinateVector 0)) • coordinateVector 0 -
  (metricPair M (coordinateVector 2) (gramSecond M) /
    metricPair M (gramSecond M) (gramSecond M)) • gramSecond M

def metricNormalize (M : R3 →L[ℝ] R3) (v : R3) : R3 :=
  (Real.sqrt (metricPair M v v))⁻¹ • v

def metricGramFrame (M : R3 →L[ℝ] R3) (i : Fin 3) : R3 :=
  if i = 0 then metricNormalize M (coordinateVector 0)
  else if i = 1 then metricNormalize M (gramSecond M) else metricNormalize M (gramThird M)

lemma coordinateVector_zero_ne : coordinateVector (0 : Fin 3) ≠ 0 := by
  intro h
  have hi := congrArg (fun v : R3 => v 0) h
  norm_num [coordinateVector, PiLp.single_apply] at hi

lemma gramSecond_one (M : R3 →L[ℝ] R3) : gramSecond M 1 = 1 := by
  simp [gramSecond, coordinateVector, PiLp.single_apply]

lemma gramSecond_two (M : R3 →L[ℝ] R3) : gramSecond M 2 = 0 := by
  simp [gramSecond, coordinateVector, PiLp.single_apply]

lemma gramSecond_ne_zero (M : R3 →L[ℝ] R3) : gramSecond M ≠ 0 := by
  intro h
  have hi := gramSecond_one M
  rw [h] at hi
  norm_num at hi

lemma gramThird_two (M : R3 →L[ℝ] R3) : gramThird M 2 = 1 := by
  simp [gramThird, coordinateVector, PiLp.single_apply, gramSecond_two]

lemma gramThird_ne_zero (M : R3 →L[ℝ] R3) : gramThird M ≠ 0 := by
  intro h
  have hi := gramThird_two M
  rw [h] at hi
  norm_num at hi

lemma metricPair_sub_left (M : R3 →L[ℝ] R3) (v w z : R3) :
    metricPair M (v-w) z = metricPair M v z - metricPair M w z := by
  simp [metricPair, inner_sub_left]

lemma metricPair_smul_left (M : R3 →L[ℝ] R3) (a : ℝ) (v w : R3) :
    metricPair M (a • v) w = a * metricPair M v w := by
  simp [metricPair, real_inner_smul_left]

lemma metricPair_normalize (M : R3 →L[ℝ] R3) (v w : R3) :
    metricPair M (metricNormalize M v) (metricNormalize M w) =
      (Real.sqrt (metricPair M v v))⁻¹ * (Real.sqrt (metricPair M w w))⁻¹ * metricPair M v w := by
  simp [metricPair, metricNormalize, real_inner_smul_left, real_inner_smul_right]
  ring

lemma metricPair_normalize_self (M : R3 →L[ℝ] R3) (v : R3)
    (hv : 0 < metricPair M v v) : metricPair M (metricNormalize M v) (metricNormalize M v) = 1 := by
  rw [metricPair_normalize]
  have hs := Real.sq_sqrt hv.le
  have hn := (Real.sqrt_pos.mpr hv).ne'
  field_simp
  nlinarith

lemma metricPair_gramSecond_zero (M : R3 →L[ℝ] R3)
    (h0 : metricPair M (coordinateVector 0) (coordinateVector 0) ≠ 0) :
    metricPair M (gramSecond M) (coordinateVector 0) = 0 := by
  rw [gramSecond, metricPair_sub_left, metricPair_smul_left]
  field_simp
  ring

lemma metricPair_gramThird_zero (M : R3 →L[ℝ] R3)
    (h0 : metricPair M (coordinateVector 0) (coordinateVector 0) ≠ 0) :
    metricPair M (gramThird M) (coordinateVector 0) = 0 := by
  simp only [gramThird, metricPair_sub_left, metricPair_smul_left, metricPair_gramSecond_zero M h0,
    mul_zero, sub_zero]
  field_simp
  ring

lemma metricPair_gramThird_second (M : R3 →L[ℝ] R3)
    (hs : ∀ v w, metricPair M v w = metricPair M w v)
    (h0 : metricPair M (coordinateVector 0) (coordinateVector 0) ≠ 0)
    (h1 : metricPair M (gramSecond M) (gramSecond M) ≠ 0) :
    metricPair M (gramThird M) (gramSecond M) = 0 := by
  have h01 : metricPair M (coordinateVector 0) (gramSecond M) = 0 := by
    rw [hs, metricPair_gramSecond_zero M h0]
  simp only [gramThird, metricPair_sub_left, metricPair_smul_left, h01, mul_zero, sub_zero]
  field_simp
  ring

theorem metricGramFrame_isMetricOrthonormalFrame (M : R3 →L[ℝ] R3)
    (hs : ∀ v w, metricPair M v w = metricPair M w v)
    (hp : ∀ v : R3, v ≠ 0 → 0 < metricPair M v v) :
    IsMetricOrthonormalFrame M (metricGramFrame M) := by
  have h0 := hp _ coordinateVector_zero_ne
  have h1 := hp _ (gramSecond_ne_zero M)
  have h2 := hp _ (gramThird_ne_zero M)
  have h10 := metricPair_gramSecond_zero M h0.ne'
  have h20 := metricPair_gramThird_zero M h0.ne'
  have h21 := metricPair_gramThird_second M hs h0.ne' h1.ne'
  have h01 : metricPair M (coordinateVector 0) (gramSecond M) = 0 := by rw [hs,h10]
  have h02 : metricPair M (coordinateVector 0) (gramThird M) = 0 := by rw [hs,h20]
  have h12 : metricPair M (gramSecond M) (gramThird M) = 0 := by rw [hs,h21]
  intro i j
  change metricPair M (metricGramFrame M i) (metricGramFrame M j) = _
  fin_cases i <;> fin_cases j <;>
    simp [metricGramFrame, metricPair_normalize_self M _ h0, metricPair_normalize_self M _ h1,
      metricPair_normalize_self M _ h2, metricPair_normalize, h10,h20,h21,h01,h02,h12]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiff_metricPair (M : E → R3 →L[ℝ] R3) (v w : E → R3)
    (hM : ContDiff ℝ ∞ M) (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x => metricPair (M x) (v x) (w x)) :=
  (hM.clm_apply hv).inner ℝ hw

lemma contDiff_gramSecond (M : E → R3 →L[ℝ] R3) (hM : ContDiff ℝ ∞ M)
    (hp : ∀ x, ∀ v : R3, v ≠ 0 → 0 < metricPair (M x) v v) :
    ContDiff ℝ ∞ (fun x => gramSecond (M x)) := by
  have hnum := contDiff_metricPair M (fun _ => coordinateVector 1) (fun _ => coordinateVector 0)
    hM contDiff_const contDiff_const
  have hden := contDiff_metricPair M (fun _ => coordinateVector 0) (fun _ => coordinateVector 0)
    hM contDiff_const contDiff_const
  exact contDiff_const.sub ((hnum.div hden (fun x => (hp x _ coordinateVector_zero_ne).ne')).smul contDiff_const)

lemma contDiff_gramThird (M : E → R3 →L[ℝ] R3) (hM : ContDiff ℝ ∞ M)
    (hp : ∀ x, ∀ v : R3, v ≠ 0 → 0 < metricPair (M x) v v) :
    ContDiff ℝ ∞ (fun x => gramThird (M x)) := by
  have h1 := contDiff_gramSecond M hM hp
  have hnum0 := contDiff_metricPair M (fun _ => coordinateVector 2) (fun _ => coordinateVector 0)
    hM contDiff_const contDiff_const
  have hden0 := contDiff_metricPair M (fun _ => coordinateVector 0) (fun _ => coordinateVector 0)
    hM contDiff_const contDiff_const
  have hnum1 := contDiff_metricPair M (fun _ => coordinateVector 2) (fun x => gramSecond (M x))
    hM contDiff_const h1
  have hden1 := contDiff_metricPair M (fun x => gramSecond (M x)) (fun x => gramSecond (M x)) hM h1 h1
  exact (contDiff_const.sub ((hnum0.div hden0 (fun x => (hp x _ coordinateVector_zero_ne).ne')).smul contDiff_const)).sub
    ((hnum1.div hden1 (fun x => (hp x _ (gramSecond_ne_zero (M x))).ne')).smul h1)

lemma contDiff_metricNormalize (M : E → R3 →L[ℝ] R3) (v : E → R3)
    (hM : ContDiff ℝ ∞ M) (hv : ContDiff ℝ ∞ v)
    (hpos : ∀ x, 0 < metricPair (M x) (v x) (v x)) :
    ContDiff ℝ ∞ (fun x => metricNormalize (M x) (v x)) := by
  have hs := (contDiff_metricPair M v v hM hv hv).sqrt (fun x => (hpos x).ne')
  exact (hs.inv (fun x => (Real.sqrt_pos.mpr (hpos x)).ne')).smul hv

lemma contDiff_metricGramFrame (M : E → R3 →L[ℝ] R3) (hM : ContDiff ℝ ∞ M)
    (hp : ∀ x, ∀ v : R3, v ≠ 0 → 0 < metricPair (M x) v v) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => metricGramFrame (M x) i) := by
  fin_cases i
  · simpa [metricGramFrame] using contDiff_metricNormalize M (fun _ => coordinateVector 0)
      hM contDiff_const (fun x => hp x _ coordinateVector_zero_ne)
  · simpa [metricGramFrame] using
      contDiff_metricNormalize M (fun x => gramSecond (M x)) hM (contDiff_gramSecond M hM hp)
        (fun x => hp x _ (gramSecond_ne_zero (M x)))
  · simpa [metricGramFrame] using contDiff_metricNormalize M (fun x => gramThird (M x)) hM
        (contDiff_gramThird M hM hp) (fun x => hp x _ (gramThird_ne_zero (M x)))

end OAI.AnisotropicCalderon.NormalCoordinatesFrame
