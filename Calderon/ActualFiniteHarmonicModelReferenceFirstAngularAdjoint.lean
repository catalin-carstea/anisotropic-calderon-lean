import Calderon.ActualFiniteHarmonicModelReferenceFirstUniformExpansion
import Calderon.ActualFiniteHarmonicModelHalfWeightSumAction

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualReferenceDDSpectralTransport ActualMixedDensityHigherCoefficientJets ActualReferenceDDHigherGeometryJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceFirstAdjointFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] referenceFirstAdjointFunction

def nativeReferenceFirstAngularAdjoint
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, nativeReferenceFrameScalar hO hD g hg L lam a j*coreDerivative hO hD hF a

lemma nativeReferenceFirstCoefficient_pointwise_inner_adjoint
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeReferenceFirstCoefficient hO hD hF g hg L lam δ R p hδ hR j F x,G x⟫_ℝ =
      ⟪F x,nativeReferenceFirstAngularAdjoint hO hD hF g hg L lam j G x⟫_ℝ := by
  unfold nativeReferenceFirstCoefficient nativeReferenceFirstAngularAdjoint
  simp only [LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,sum_inner,inner_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hc : Commute (coreRaising hO hD hF a) (nativeReferenceFrameScalar hO hD g hg L lam a j) := by
    unfold nativeReferenceFrameScalar
    exact scalarCentral_coreRaising hO hD hF a _ _
  rw [hc.eq]
  simp only [Module.End.mul_apply,nativeReferenceFrameScalar,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_mk,real_inner_smul_left,real_inner_smul_right]
  congr 1
  exact (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (Sum.inr (Sum.inl a)) x).2.1 F G

theorem exists_nativeReferenceFirstAngularAdjoint_uniform_half_norm_bound
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ j : Fin 3,
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (nativeReferenceFirstAngularAdjoint hO hD hF g hg L lam j F) x‖ ≤
        C*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  obtain ⟨M,hM,hbound⟩ := exists_mixed_background_coordinate_jet_bound g hg L K hK 0
  refine ⟨6*M,by have hm : 0 < M := lt_of_lt_of_le zero_lt_one hM; positivity,?_⟩
  intro lam hlam x hx j F
  have hz : PreservesSphereSpectralGraphs hO hD (0 : SphereL2 →L[ℝ] SphereL2) := by
    intro w u v huv
    change (0 : SphereL2 × SphereL2) ∈ spectralGraph hO hD w
    exact (spectralGraph hO hD w).zero_mem
  have he : nativeReferenceFirstAngularAdjoint hO hD hF g hg L lam j F x =
      (0 : SphereL2 →L[ℝ] SphereL2) (coreWeightOperator hO hD (besselWeight 1) F x)+
        ∑ a : Fin 3, referenceMetricGramFrame g L (lam,x) a j • coreDerivative hO hD hF a F x := by
    simp only [nativeReferenceFirstAngularAdjoint,LinearMap.sum_apply,Module.End.mul_apply,
      nativeReferenceFrameScalar,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
      Submodule.coe_sum,Finset.sum_apply,ContinuousLinearMap.zero_apply,zero_add]
  have ht := norm_coreWeight_half_le_preserving_add_sum hO hD 0 hz
    (nativeReferenceFirstAngularAdjoint hO hD hF g hg L lam j F) F
    (fun a : Fin 3 => coreDerivative hO hD hF a F)
    (fun a : Fin 3 => referenceMetricGramFrame g L (lam,x) a j) (fun _ => 2) x he
    (fun a => norm_coreWeight_half_derivative_le hO hD hF a F x)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    mul_le_mul_of_nonneg_right ((hbound lam hlam x hx).1 [] (by simp) a j) (by norm_num : (0 : ℝ) ≤ 2))
  simp only [coordinateFieldWordPartial,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  simp only [norm_zero,zero_add] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right (by nlinarith : (∑ a : Fin 3, |referenceMetricGramFrame g L (lam,x) a j| *2) ≤ 6*M) (norm_nonneg _))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
