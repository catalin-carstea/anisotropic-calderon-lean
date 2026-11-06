import Calderon.IntervalDistributionConstancy
import Calderon.ActualRadialTestIntegration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter TopologicalSpace intervalIntegral
open scoped ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.IntervalDistributionPrimitive
open IntervalDistributionConstancy

/-! Expanded before source in EXPANSION-interval-distribution-primitive-v001.json. -/

def intervalPrimitive (D : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s in (0 : ℝ)..r, D s

theorem continuousOn_intervalPrimitive (D : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hD : ContinuousOn D (Icc (0 : ℝ) R)) :
    ContinuousOn (intervalPrimitive D) (Icc (0 : ℝ) R) := by
  have hi : IntegrableOn D (uIcc (0 : ℝ) R) := by
    rw [uIcc_of_le hR]
    exact hD.integrableOn_compact isCompact_Icc
  change ContinuousOn (fun r => ∫ s in (0 : ℝ)..r, D s) (Icc (0 : ℝ) R)
  simpa only [uIcc_of_le hR] using continuousOn_primitive_interval hi

theorem hasDerivAt_intervalPrimitive (D : ℝ → ℝ) (R : ℝ)
    (hD : ContinuousOn D (Icc (0 : ℝ) R)) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    HasDerivAt (intervalPrimitive D) (D r) r := by
  have hint : IntervalIntegrable D volume 0 r := by
    apply ContinuousOn.intervalIntegrable_of_Icc hr.1.le
    exact hD.mono (Icc_subset_Icc le_rfl hr.2.le)
  have hc : ContinuousAt D r := hD.continuousAt (Icc_mem_nhds hr.1 hr.2)
  have hm : StronglyMeasurableAtFilter D (𝓝 r) (volume : Measure ℝ) :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hD.mono Ioo_subset_Icc_self) r hr
  exact integral_hasDerivAt_right hint hm hc

def intervalTestFunction (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (R : ℝ)
    (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R) :
    𝓓((⟨Ioo (0 : ℝ) R,isOpen_Ioo⟩ : Opens ℝ), ℝ) where
  toFun := ψ
  contDiff' := hψ
  hasCompactSupport' := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ)
    (hψs.trans Ioo_subset_Icc_self)
  tsupport_subset' := hψs

theorem integral_test_intervalPrimitive (D : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hD : ContinuousOn D (Icc (0 : ℝ) R))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R) :
    (∫ r : ℝ, deriv ψ r * intervalPrimitive D r) = -(∫ r : ℝ, ψ r * D r) := by
  let Ω : Opens ℝ := ⟨Ioo (0 : ℝ) R,isOpen_Ioo⟩
  let φ : 𝓓(Ω, ℝ) := intervalTestFunction ψ hψ R hψs
  have hPc : ContinuousOn (intervalPrimitive D) (Ioo (0 : ℝ) R) :=
    (continuousOn_intervalPrimitive D R hR.le hD).mono Ioo_subset_Icc_self
  have hDc : ContinuousOn D (Ioo (0 : ℝ) R) := hD.mono Ioo_subset_Icc_self
  have hw : TauCeti.HasWeakLineDerivOn (volume : Measure ℝ) Ω
      (intervalPrimitive D) D (1 : ℝ) :=
    TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
      (hPc.locallyIntegrableOn measurableSet_Ioo) (hDc.locallyIntegrableOn measurableSet_Ioo)
      (fun r hr => by
        have h := (hasDerivAt_intervalPrimitive D R hD r hr).hasFDerivAt.hasLineDerivAt (1 : ℝ)
        simpa using h)
  have hl (r : ℝ) : lineDeriv ℝ (φ : ℝ → ℝ) r (1 : ℝ) = deriv ψ r := by
    have h := ((hψ.differentiable (by simp) r).hasDerivAt.hasFDerivAt.hasLineDerivAt (1 : ℝ)).lineDeriv
    change lineDeriv ℝ ψ r (1 : ℝ) = deriv ψ r
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h
  have hi := hw.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp_rw [hl, smul_eq_mul] at hi
  exact hi

theorem eq_intervalPrimitive_of_integral_test (G D : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hG : ContinuousOn G (Icc (0 : ℝ) R)) (hD : ContinuousOn D (Icc (0 : ℝ) R))
    (hG0 : G 0 = 0)
    (hDist : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo (0 : ℝ) R →
      (∫ r : ℝ, ψ r * D r) = -(∫ r : ℝ, deriv ψ r * G r)) :
    EqOn G (intervalPrimitive D) (Icc (0 : ℝ) R) := by
  have hP := continuousOn_intervalPrimitive D R hR.le hD
  have hH : ContinuousOn (fun r : ℝ => G r - intervalPrimitive D r) (Icc (0 : ℝ) R) :=
    hG.sub hP
  obtain ⟨c,hc⟩ := exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero
    (hH.mono Ioo_subset_Icc_self) (fun ψ hψ hψs => by
      let Ω : Opens ℝ := ⟨Ioo (0 : ℝ) R,isOpen_Ioo⟩
      let φ : 𝓓(Ω, ℝ) := intervalTestFunction ψ hψ R hψs
      have hl (r : ℝ) : lineDeriv ℝ (φ : ℝ → ℝ) r (1 : ℝ) = deriv ψ r := by
        have h := ((hψ.differentiable (by simp) r).hasDerivAt.hasFDerivAt.hasLineDerivAt (1 : ℝ)).lineDeriv
        change lineDeriv ℝ ψ r (1 : ℝ) = deriv ψ r
        simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h
      have hIG : Integrable (fun r : ℝ => deriv ψ r * G r) := by
        have h := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
          (μ := (volume : Measure ℝ))
          ((hG.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo) φ (1 : ℝ)
        simpa only [hl, smul_eq_mul] using h
      have hIP : Integrable (fun r : ℝ => deriv ψ r * intervalPrimitive D r) := by
        have h := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
          (μ := (volume : Measure ℝ))
          ((hP.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo) φ (1 : ℝ)
        simpa only [hl, smul_eq_mul] using h
      have hi := integral_test_intervalPrimitive D R hR hD ψ hψ hψs
      rw [hDist ψ hψ hψs, neg_neg] at hi
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub hIG hIP, hi, sub_self])
  have hclosed : EqOn (fun r : ℝ => G r - intervalPrimitive D r) (fun _ => c)
      (Icc (0 : ℝ) R) := hc.of_subset_closure hH continuousOn_const Ioo_subset_Icc_self (by
        rw [closure_Ioo hR.ne])
  have hc0 : c = 0 := by
    have hz := hclosed ⟨le_rfl,hR.le⟩
    simpa only [hG0, intervalPrimitive, integral_same, sub_zero] using hz.symm
  intro r hr
  exact sub_eq_zero.mp (by simpa only [hc0] using hclosed hr)

end OAI.AnisotropicCalderon.IntervalDistributionPrimitive

#print axioms OAI.AnisotropicCalderon.IntervalDistributionPrimitive.intervalPrimitive
#print axioms OAI.AnisotropicCalderon.IntervalDistributionPrimitive.continuousOn_intervalPrimitive
#print axioms OAI.AnisotropicCalderon.IntervalDistributionPrimitive.hasDerivAt_intervalPrimitive
#print axioms OAI.AnisotropicCalderon.IntervalDistributionPrimitive.intervalTestFunction
#print axioms OAI.AnisotropicCalderon.IntervalDistributionPrimitive.integral_test_intervalPrimitive
#print axioms OAI.AnisotropicCalderon.IntervalDistributionPrimitive.eq_intervalPrimitive_of_integral_test
