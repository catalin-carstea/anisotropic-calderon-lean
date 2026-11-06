import Calderon.ActualOriginalFiniteReferenceModelDefinitions
import Calderon.ActualFiniteHarmonicModelPerturbedGain

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev modelNormComparisonFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] modelNormComparisonFunction


def nativeModelAdjoint
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  2*nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR+
    nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR

lemma nativeModelRaising_density_adjoint
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
      ⟪nativeModelRaising hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,G x⟫_ℝ) =
    ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
      ⟪nativeModelAdjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR G x,F x⟫_ℝ := by
  let qG := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam G
  let qF := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let T := nativeT hO hD hF g1 hg1 L lam δ R p hδ hR
  let Td := nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR
  let U := nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let Ud := nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hT : qG (T F)=qF (Td G) := by
    calc
      _ = ∫ x : R3, referenceDensityFamily g1 L (lam,x)*⟪F x,Td G x⟫_ℝ :=
        compact_nativeT_adjoint hO hD hF g1 hg1 L lam δ R p hδ hR F G
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg (fun a : ℝ => referenceDensityFamily g1 L (lam,x)*a) (real_inner_comm _ _))
  have hU : qG (U F)=qF (Ud G) := by
    calc
      _ = ∫ x : R3, referenceDensityFamily g1 L (lam,x)*⟪F x,Ud G x⟫_ℝ :=
        compact_nativeU_adjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F G
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg (fun a : ℝ => referenceDensityFamily g1 L (lam,x)*a) (real_inner_comm _ _))
  change qG ((2*T+U) F)=qF ((2*Td+Ud) G)
  simp only [two_mul,LinearMap.add_apply,map_add,hT,hU]

lemma nativePerturbedGain_density_pair_eq_model_norms
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (F : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
      ⟪nativePerturbedGain hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ) =
      (∫ x : R3, referenceDensityFamily g1 L (lam,x)*‖nativeModelRaising hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x‖^2)-
      (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
        ‖nativeModelAdjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x+(2:ℝ) • nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2)+
      4*(∫ x : R3, referenceDensityFamily g1 L (lam,x)*‖nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2) := by
  let T := nativeModelRaising hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let Td := nativeModelAdjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let Z := nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR
  let Zd := nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR
  let rho : R3 → ℝ := fun x => referenceDensityFamily g1 L (lam,x)
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  have hTT : q (Td (T F))=∫ x : R3, rho x*‖T F x‖^2 := by
    have ht := nativeModelRaising_density_adjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F (T F)
    change (∫ x : R3, rho x*⟪T F x,T F x⟫_ℝ)=q (Td (T F)) at ht
    simpa only [real_inner_self_eq_norm_sq] using ht.symm
  have hTdTd : q (T (Td F))=∫ x : R3, rho x*‖Td F x‖^2 := by
    have ht := nativeModelRaising_density_adjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR (Td F) F
    change q (T (Td F))=(∫ x : R3, rho x*⟪Td F x,Td F x⟫_ℝ) at ht
    simpa only [real_inner_self_eq_norm_sq] using ht
  have hTZ : q (T (Z F))=∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ := by
    have ht := nativeModelRaising_density_adjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR (Z F) F
    change q (T (Z F))=(∫ x : R3, rho x*⟪Td F x,Z F x⟫_ℝ) at ht
    calc
      _ = _ := ht
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg (fun a : ℝ => rho x*a) (real_inner_comm _ _))
  have hZdTd : q (Zd (Td F))=∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ := by
    change (∫ x : R3, rho x*⟪Zd (Td F) x,F x⟫_ℝ)=_
    calc
      _ = ∫ x : R3, rho x*⟪F x,Zd (Td F) x⟫_ℝ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg (fun a : ℝ => rho x*a) (real_inner_comm _ _))
      _ = _ := (compact_nativeZ_adjoint hO hD hF g1 hg1 L lam δ R p hδ hR F (Td F)).symm
  have hrho : Continuous rho := WeightedBaseSpectral.continuous_referenceBaseDensity g1 hg1 L lam
  have hY := integrable_native_core_weighted_norm_sq hO hD rho hrho (Td F)
  have hZ := integrable_native_core_weighted_norm_sq hO hD rho hrho (Z F)
  have hYZ := integrable_native_core_density_pair hO hD g1 hg1 L lam (Z F) (Td F)
  change Integrable (fun x : R3 => rho x*⟪Z F x,Td F x⟫_ℝ) at hYZ
  have hsum : (∫ x : R3, rho x*‖Td F x+(2:ℝ) • Z F x‖^2)=
      (∫ x : R3, rho x*‖Td F x‖^2)+4*(∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ)+
        4*(∫ x : R3, rho x*‖Z F x‖^2) := by
    calc
      _ = ∫ x : R3, ((rho x*‖Td F x‖^2)+4*(rho x*⟪Z F x,Td F x⟫_ℝ))+4*(rho x*‖Z F x‖^2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [norm_add_sq_real,real_inner_smul_right,real_inner_comm (Td F x) (Z F x),norm_smul]
        norm_num [Real.norm_eq_abs]
        ring
      _ = _ := by
        have he := integral_add (hY.add (hYZ.const_mul 4)) (hZ.const_mul 4)
        simp only [Pi.add_apply] at he
        rw [integral_add hY (hYZ.const_mul 4),integral_const_mul,integral_const_mul] at he
        exact he
  have hcomm0 (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      ActualModelCommutatorWords.commutator (A-B) B=A*B-B*A := by
    unfold ActualModelCommutatorWords.commutator
    noncomm_ring [smul_add,neg_add_rev]
  have hcomm := hcomm0 Td T
  change q ((ActualModelCommutatorWords.commutator (Td-T) T-2*(T*Z+Zd*Td)) F)=_
  rw [hcomm]
  simp only [two_mul,LinearMap.sub_apply,LinearMap.add_apply,Module.End.mul_apply,map_sub,map_add]
  rw [hTT,hTdTd,hTZ,hZdTd]
  change (∫ x : R3, rho x*‖T F x‖^2)-(∫ x : R3, rho x*‖Td F x‖^2)-
    (((∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ)+(∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ))+
     ((∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ)+(∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ))) =
    (∫ x : R3, rho x*‖T F x‖^2)-(∫ x : R3, rho x*‖Td F x+(2:ℝ) • Z F x‖^2)+
      4*(∫ x : R3, rho x*‖Z F x‖^2)
  linarith

lemma nativeModel_norm_comparison
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (F : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, referenceDensityFamily g1 L (lam,x)*‖nativeModelRaising hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x‖^2)-
      (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
        ‖nativeModelAdjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x+(2:ℝ) • nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2) =
      4*((∫ x : R3, referenceDensityFamily g1 L (lam,x)*‖nativeT hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2)-
        (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
          ‖nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR F x+nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x‖^2))+
      (∫ x : R3, referenceDensityFamily g1 L (lam,x)*
        ⟪nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ) := by
  have hQ := nativePerturbedGain_density_pair_eq hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F
  rw [nativePerturbedGain_density_pair_eq_model_norms hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F,
    nativeReferenceGain_density_pair_eq hO hD hF g1 hg1 L lam δ R p hδ hR F] at hQ
  linarith

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
