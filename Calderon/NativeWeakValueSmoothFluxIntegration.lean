import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes native-value integration against an actual smooth flux. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal ContDiff Distributions Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume

theorem nativeWeakValue_smoothFlux_compactTest_integration
    (Ω : Opens R3) (u : TauCeti.W1p (volume : Measure R3) Ω 2)
    (J : Fin 3 → R3 → ℝ) (hJ : ∀ i : Fin 3, ContDiff ℝ ∞ (J i)) (φ : 𝓓(Ω, ℝ)) :
    (∫ x in Ω, TauCeti.W1p.value u x *
      (∑ i : Fin 3, (⟪gradient (φ : R3 → ℝ) x,coordinateVector i⟫_ℝ * J i x +
        φ x * lineDeriv ℝ (J i) x (coordinateVector i))) ∂(volume : Measure R3)) =
      -(∫ x in Ω, φ x *
        (∑ i : Fin 3, ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ * J i x)
        ∂(volume : Measure R3)) := by
  have hSupp (i : Fin 3) : Function.support (fun x : R3 => φ x * J i x) ⊆
      tsupport (φ : R3 → ℝ) := by
    intro x hx
    apply subset_tsupport (φ : R3 → ℝ)
    intro hzero
    exact hx (by
      change φ x * J i x = 0
      rw [hzero,zero_mul])
  let τ : Fin 3 → 𝓓(Ω, ℝ) := fun i =>
    ⟨fun x => φ x * J i x, φ.contDiff.mul (hJ i),
      φ.hasCompactSupport.mono' (hSupp i),
      (closure_minimal (hSupp i) (isClosed_tsupport (φ : R3 → ℝ))).trans φ.tsupport_subset⟩
  have hτ (i : Fin 3) : (τ i : R3 → ℝ) = fun x => φ x * J i x := rfl
  have hLoc := (TauCeti.W1p.hasWeakFDerivOn u).locallyIntegrableOn
  have hKey (i : Fin 3) :
      (∫ x in Ω, lineDeriv ℝ (τ i : R3 → ℝ) x (coordinateVector i) •
        TauCeti.W1p.value u x ∂(volume : Measure R3)) =
      -(∫ x in Ω, (τ i : R3 → ℝ) x •
        ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ ∂(volume : Measure R3)) := by
    rw [TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
      TauCeti.setIntegral_smul_eq_integral_smul,
      ((TauCeti.W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (coordinateVector i)).integral_lineDeriv_smul_eq_neg_integral_smul (τ i)]
    simp only [innerSL_apply_apply]
  have hDeriv (i : Fin 3) (x : R3) :
      lineDeriv ℝ (τ i : R3 → ℝ) x (coordinateVector i) =
        ⟪gradient (φ : R3 → ℝ) x,coordinateVector i⟫_ℝ * J i x +
          φ x * lineDeriv ℝ (J i) x (coordinateVector i) := by
    have hφx : DifferentiableAt ℝ (φ : R3 → ℝ) x := (φ.contDiff.differentiable (by simp)) x
    have hJx : DifferentiableAt ℝ (J i) x := ((hJ i).differentiable (by simp)) x
    have hmul : DifferentiableAt ℝ (fun y : R3 => φ y * J i y) x := hφx.mul hJx
    rw [hτ,hmul.lineDeriv_eq_fderiv,hJx.lineDeriv_eq_fderiv,
      fderiv_fun_mul hφx hJx,inner_gradient_left]
    simp only [_root_.add_apply,smul_apply,smul_eq_mul]
    ring
  have hInt1 (i : Fin 3) : Integrable
      (fun x => lineDeriv ℝ (τ i : R3 → ℝ) x (coordinateVector i) • TauCeti.W1p.value u x)
      ((volume : Measure R3).restrict Ω) :=
    (TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn hLoc (τ i) (coordinateVector i)).restrict
  have hInt2 (i : Fin 3) : Integrable
      (fun x => (τ i : R3 → ℝ) x • ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ)
      ((volume : Measure R3).restrict Ω) :=
    (TauCeti.integrable_smul_of_locallyIntegrableOn
      (w := fun x => ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ)
      (by simpa only [innerSL_apply_apply] using
        ((TauCeti.W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (coordinateVector i)).locallyIntegrableOn_deriv)
      (τ i)).restrict
  calc
    _ = ∫ x in Ω, ∑ i : Fin 3,
        lineDeriv ℝ (τ i : R3 → ℝ) x (coordinateVector i) • TauCeti.W1p.value u x
        ∂(volume : Measure R3) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        simp only [hDeriv,smul_eq_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring)
    _ = ∑ i : Fin 3, ∫ x in Ω,
        lineDeriv ℝ (τ i : R3 → ℝ) x (coordinateVector i) • TauCeti.W1p.value u x
        ∂(volume : Measure R3) := integral_finsetSum _ (fun i _ => hInt1 i)
    _ = ∑ i : Fin 3, -(∫ x in Ω, (τ i : R3 → ℝ) x •
        ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ ∂(volume : Measure R3)) :=
      Finset.sum_congr rfl (fun i _ => hKey i)
    _ = -(∫ x in Ω, ∑ i : Fin 3, (τ i : R3 → ℝ) x •
        ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ ∂(volume : Measure R3)) := by
      rw [integral_finsetSum _ (fun i _ => hInt2 i),Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        simp only [hτ,smul_eq_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring)

end OAI.AnisotropicCalderon.ExteriorSource
