import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.Sobolev.W1p.Zero

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

lemma nativeTest_sub_value_ae
    (phi : 𝓓(Omega, ℝ)) (v : TauCeti.W1p mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega,
      TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi-v) x =
        phi x-TauCeti.W1p.value v x := by
  have hSub : TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi-v) =
      TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi)-TauCeti.W1p.value v := by
    simp only [← TauCeti.W1p.valueL_apply,map_sub]
  rw [hSub]
  filter_upwards [Lp.coeFn_sub
    (TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi))
    (TauCeti.W1p.value v), TauCeti.testFunctionLp_apply_ae (mu := mu) 2 phi]
    with x hSubX hPhi
  rw [hSubX,Pi.sub_apply,TauCeti.W1p.value_ofTestFunctionₗ,hPhi]

lemma nativeTest_posPart_sub_zero_off_tsupport_ae
    (phi : 𝓓(Omega, ℝ)) (v : TauCeti.W1p mu Omega 2)
    (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ TauCeti.W1p.value v x) :
    ∀ᵐ x ∂mu.restrict Omega, x ∉ tsupport phi →
      TauCeti.W1p.value (TauCeti.W1p.posPart
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi-v)) x = 0 := by
  let hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hPos : ∀ᵐ x ∂mu.restrict Omega,
      TauCeti.W1p.value (TauCeti.W1p.posPart hp
        (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi-v)) x =
      max (TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ mu Omega 2 phi-v) x) 0 := by
    rw [TauCeti.W1p.value_posPart]
    exact Lp.coeFn_posPart _
  filter_upwards [nativeTest_sub_value_ae phi v,hPos,hv] with x hValueX hPosX hV
  intro hx
  rw [hPosX,hValueX,image_eq_zero_of_notMem_tsupport hx,zero_sub]
  exact max_eq_right (neg_nonpos.mpr hV)

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.nativeTest_sub_value_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.nativeTest_posPart_sub_zero_off_tsupport_ae
