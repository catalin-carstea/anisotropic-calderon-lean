import Calderon.ActualFiniteHarmonicModelReferenceEnergyRepresentative
import Calderon.ActualFiniteHarmonicModelDensityPairLinearMap

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceGainFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] referenceGainFunction

def nativeReferenceGain (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  let T := nativeT hO hD hF g hg L lam δ R p hδ hR
  let Td := nativeTdag hO hD hF g hg L lam δ R p hδ hR
  let Z := nativeZ hO hD hF g hg L lam δ R p hδ hR
  let Zd := nativeZdag hO hD hF g hg L lam δ R p hδ hR
  ActualModelCommutatorWords.commutator Td T-(T*Z+Zd*Td)

lemma nativeReferenceGain_density_pair_eq
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, referenceDensityFamily g L (lam,x)*
      ⟪nativeReferenceGain hO hD hF g hg L lam δ R p hδ hR F x,F x⟫_ℝ) =
      (∫ x : R3, referenceDensityFamily g L (lam,x)*‖nativeT hO hD hF g hg L lam δ R p hδ hR F x‖^2)-
      (∫ x : R3, referenceDensityFamily g L (lam,x)*
        ‖nativeTdag hO hD hF g hg L lam δ R p hδ hR F x+nativeZ hO hD hF g hg L lam δ R p hδ hR F x‖^2)+
      (∫ x : R3, referenceDensityFamily g L (lam,x)*‖nativeZ hO hD hF g hg L lam δ R p hδ hR F x‖^2) := by
  let T := nativeT hO hD hF g hg L lam δ R p hδ hR
  let Td := nativeTdag hO hD hF g hg L lam δ R p hδ hR
  let Z := nativeZ hO hD hF g hg L lam δ R p hδ hR
  let Zd := nativeZdag hO hD hF g hg L lam δ R p hδ hR
  let rho : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let q := nativeCoreDensityPairLinearMap hO hD g hg L lam F
  have hTT : q (Td (T F))=∫ x : R3, rho x*‖T F x‖^2 := by
    change (∫ x : R3, rho x*⟪Td (T F) x,F x⟫_ℝ)=_
    calc
      _ = ∫ x : R3, rho x*⟪F x,Td (T F) x⟫_ℝ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg (fun a : ℝ => rho x*a) (real_inner_comm _ _))
      _ = ∫ x : R3, rho x*⟪T F x,T F x⟫_ℝ := (compact_nativeT_adjoint hO hD hF g hg L lam δ R p hδ hR F (T F)).symm
      _ = _ := by simp only [real_inner_self_eq_norm_sq]
  have hTdTd : q (T (Td F))=∫ x : R3, rho x*‖Td F x‖^2 := by
    change (∫ x : R3, rho x*⟪T (Td F) x,F x⟫_ℝ)=_
    have ht := compact_nativeT_adjoint hO hD hF g hg L lam δ R p hδ hR (Td F) F
    change (∫ x : R3, rho x*⟪T (Td F) x,F x⟫_ℝ)=(∫ x : R3, rho x*⟪Td F x,Td F x⟫_ℝ) at ht
    simpa only [real_inner_self_eq_norm_sq] using ht
  have hTZ : q (T (Z F))=∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ :=
    compact_nativeT_adjoint hO hD hF g hg L lam δ R p hδ hR (Z F) F
  have hZdTd : q (Zd (Td F))=∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ := by
    change (∫ x : R3, rho x*⟪Zd (Td F) x,F x⟫_ℝ)=_
    calc
      _ = ∫ x : R3, rho x*⟪F x,Zd (Td F) x⟫_ℝ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg (fun a : ℝ => rho x*a) (real_inner_comm _ _))
      _ = _ := (compact_nativeZ_adjoint hO hD hF g hg L lam δ R p hδ hR F (Td F)).symm
  have hrho : Continuous rho := WeightedBaseSpectral.continuous_referenceBaseDensity g hg L lam
  have hY := integrable_native_core_weighted_norm_sq hO hD rho hrho (Td F)
  have hZ := integrable_native_core_weighted_norm_sq hO hD rho hrho (Z F)
  have hYZ := integrable_native_core_density_pair hO hD g hg L lam (Z F) (Td F)
  change Integrable (fun x : R3 => rho x*⟪Z F x,Td F x⟫_ℝ) at hYZ
  have hsum : (∫ x : R3, rho x*‖Td F x+Z F x‖^2)=
      (∫ x : R3, rho x*‖Td F x‖^2)+2*(∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ)+
        (∫ x : R3, rho x*‖Z F x‖^2) := by
    calc
      _ = ∫ x : R3, ((rho x*‖Td F x‖^2)+2*(rho x*⟪Z F x,Td F x⟫_ℝ))+rho x*‖Z F x‖^2 := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [norm_add_sq_real,real_inner_comm (Td F x) (Z F x)]
        ring
      _ = _ := by
        have he := integral_add (hY.add (hYZ.const_mul 2)) hZ
        simp only [Pi.add_apply] at he
        rw [integral_add hY (hYZ.const_mul 2),integral_const_mul] at he
        exact he
  change q ((Td*T-T*Td-(T*Z+Zd*Td)) F)=_
  simp only [LinearMap.sub_apply,LinearMap.add_apply,Module.End.mul_apply,map_sub,map_add]
  rw [hTT,hTdTd,hTZ,hZdTd]
  change (∫ x : R3, rho x*‖T F x‖^2)-(∫ x : R3, rho x*‖Td F x‖^2)-
    ((∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ)+(∫ x : R3, rho x*⟪Z F x,Td F x⟫_ℝ)) =
    (∫ x : R3, rho x*‖T F x‖^2)-(∫ x : R3, rho x*‖Td F x+Z F x‖^2)+(∫ x : R3, rho x*‖Z F x‖^2)
  linarith

lemma nativeReference_energy_difference_le_gain_pair
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, referenceDensityFamily g L (lam,x)*‖nativeT hO hD hF g hg L lam δ R p hδ hR F x‖^2)-
      (∫ x : R3, referenceDensityFamily g L (lam,x)*
        ‖nativeTdag hO hD hF g hg L lam δ R p hδ hR F x+nativeZ hO hD hF g hg L lam δ R p hδ hR F x‖^2) ≤
      ∫ x : R3, referenceDensityFamily g L (lam,x)*⟪nativeReferenceGain hO hD hF g hg L lam δ R p hδ hR F x,F x⟫_ℝ := by
  rw [nativeReferenceGain_density_pair_eq hO hD hF g hg L lam δ R p hδ hR F]
  have hn : 0 ≤ ∫ x : R3, referenceDensityFamily g L (lam,x)*‖nativeZ hO hD hF g hg L lam δ R p hδ hR F x‖^2 :=
    integral_nonneg (fun x => mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le (sq_nonneg _))
  linarith

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
