import Calderon.ActualFiniteHarmonicModelBZScalarActions
import Calderon.ActualFiniteHarmonicModelHalfShiftNorms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualModelCommutatorWords PrincipalCommutator AmbientReferenceRaising
  ConformalDepth SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds
  ReferenceWeightedApproximation ActualReferenceDDHigherLogFrameJets ActualReferenceDDHigherGeometryJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev zHalfNormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] zHalfNormFunction

lemma coreWeight_nativeZ_scalar_angular_action
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (w : ℕ → ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD w (nativeZ hO hD hF g hg L lam δ R p hδ hR F) x =
      ∑ a : Fin 3, referenceFrameDerivative g L lam a
        (fun y => Real.log (referenceRadius δ R p L y)) x •
        coreWeightOperator hO hD w (coreDerivative hO hD hF a F) x := by
  have hZ : nativeZ hO hD hF g hg L lam δ R p hδ hR =
      coreDefectAction hO hD hF g hg L lam δ R p hδ hR := by
    apply LinearMap.ext
    intro G
    apply Subtype.ext
    exact nativeZField_eq_coreAction hO hD hF g hg L lam δ R p hδ hR G
  have hterm (a : Fin 3) : coreWeightOperator hO hD w
      (coreScalar hO hD
        (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)))
        (contDiff_referenceFrameDerivative g hg L lam a _
          (contDiff_log_referenceRadius_profile δ R L p hδ hR))
        (coreDerivative hO hD hF a F)) x =
      referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
        coreWeightOperator hO hD w (coreDerivative hO hD hF a F) x :=
    by
      let c := referenceFrameDerivative g L lam a
        (fun y => Real.log (referenceRadius δ R p L y))
      have hc : ContDiff ℝ ∞ c := contDiff_referenceFrameDerivative g hg L lam a _
        (contDiff_log_referenceRadius_profile δ R L p hδ hR)
      have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) =>
        T (coreDerivative hO hD hF a F))
        (scalarCentral_coreWeightOperator hO hD w c hc).eq
      have hx := congrArg (fun G : smoothCompactFiniteSphereCore hO hD => G.val x) he
      simpa only [Module.End.mul_apply, coreScalar, LinearMap.coe_mk,
        AddHom.coe_mk, Submodule.coe_mk] using hx
  rw [hZ]
  simp only [coreDefectAction,Module.End.mul_apply,LinearMap.sum_apply,map_sum,
    Submodule.coe_sum,Finset.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => hterm a)

theorem exists_nativeZ_uniform_half_norm_bound
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (nativeZ hO hD hF g hg L lam δ R p hδ hR F) x‖ ≤
        (C*beta)*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  obtain ⟨J,hJ,hLog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g hg L hL K hK 0
  refine ⟨6*J,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb F
  have hf (a : Fin 3) : |referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ J*beta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one,beta,actualReferenceBeta] using
      (hLog lam hlam δ hδ hδ1 R hR p hp x hx hb [] (by simp)).1 a
  have hterm (a : Fin 3) :
      ‖referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF a F) x‖ ≤
      (2*J*beta)*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    have ht := mul_le_mul (hf a) (norm_coreWeight_half_derivative_le hO hD hF a F x)
      (norm_nonneg _) (mul_nonneg hJ.le (le_trans zero_le_one hb))
    calc
      _ ≤ (J*beta)*(2*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖) := ht
      _ = _ := by ring
  rw [coreWeight_nativeZ_scalar_angular_action]
  calc
    _ ≤ ∑ a : Fin 3, ‖referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x •
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF a F) x‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin 3, (2*J*beta)*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ :=
      Finset.sum_le_sum (fun a _ => hterm a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
