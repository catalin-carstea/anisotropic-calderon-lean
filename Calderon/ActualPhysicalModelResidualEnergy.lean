import Calderon.ActualNativePacketModelResidual
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ReferenceDensityBounds ConformalDepth

theorem referenceDensity_integrable_normSq_of_smooth_compact
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L q:ℝ)
    (f:R3→SphereL2) (hf:ContDiff ℝ ∞ f) (hc:HasCompactSupport f):
    Integrable (fun y=>referenceDensityFamily g L (q,y)*‖f y‖^2) := by
  have hw:Continuous (fun y:R3=>referenceDensityFamily g L (q,y)):=
    (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)
  apply (hw.mul (hf.continuous.norm.pow 2)).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro hc.isCompact
  intro y hy
  change referenceDensityFamily g L (q,y)*‖f y‖^2=0
  rw [image_eq_zero_of_notMem_tsupport hy,norm_zero,zero_pow (by decide:2≠0),mul_zero]

theorem referenceDensity_integrable_model_error_pairing
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L q:ℝ)
    (m e:R3→SphereL2) (hm:ContDiff ℝ ∞ m) (he:ContDiff ℝ ∞ e)
    (hc:HasCompactSupport m):
    Integrable (fun y=>referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)) := by
  have hw:Continuous (fun y:R3=>referenceDensityFamily g L (q,y)):=
    (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)
  apply (hw.mul (hm.continuous.inner he.continuous)).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro hc.isCompact
  intro y hy
  change referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)=0
  rw [image_eq_zero_of_notMem_tsupport hy,inner_zero_left,mul_zero]

theorem referenceDensity_full_output_energy_eq_model_error_energy
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L q:ℝ)
    (f m e:R3→SphereL2) (hm:ContDiff ℝ ∞ m) (he:ContDiff ℝ ∞ e)
    (hmc:HasCompactSupport m) (hec:HasCompactSupport e)
    (hEq:∀ y:R3,f y=m y+e y):
    (∫ y,referenceDensityFamily g L (q,y)*‖f y‖^2)=
      (∫ y,referenceDensityFamily g L (q,y)*‖m y‖^2)+
      2*(∫ y,referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y))+
      (∫ y,referenceDensityFamily g L (q,y)*‖e y‖^2) := by
  have hM:=referenceDensity_integrable_normSq_of_smooth_compact g hg L q m hm hmc
  have hE:=referenceDensity_integrable_normSq_of_smooth_compact g hg L q e he hec
  have hPair:=referenceDensity_integrable_model_error_pairing g hg L q m e hm he hmc
  have hFun:(fun y=>referenceDensityFamily g L (q,y)*‖f y‖^2)=
      (fun y=>(referenceDensityFamily g L (q,y)*‖m y‖^2+
        2*(referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)))+
        referenceDensityFamily g L (q,y)*‖e y‖^2):=by
    funext y
    rw [hEq y,norm_add_sq_real]
    ring
  have hTwo:(∫ y,2*(referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)))=
      2*(∫ y,referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)):=integral_const_mul _ _
  have hInner:(∫ y,referenceDensityFamily g L (q,y)*‖m y‖^2+
      2*(referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)))=
      (∫ y,referenceDensityFamily g L (q,y)*‖m y‖^2)+
      2*(∫ y,referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)):=
    (integral_add hM (hPair.const_mul 2)).trans
      (congrArg (fun v=>(∫ y,referenceDensityFamily g L (q,y)*‖m y‖^2)+v) hTwo)
  have hOuter:(∫ y,(referenceDensityFamily g L (q,y)*‖m y‖^2+
      2*(referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)))+
      referenceDensityFamily g L (q,y)*‖e y‖^2)=
      (∫ y,referenceDensityFamily g L (q,y)*‖m y‖^2+
        2*(referenceDensityFamily g L (q,y)*inner ℝ (m y) (e y)))+
      (∫ y,referenceDensityFamily g L (q,y)*‖e y‖^2):=
    integral_add (hM.add (hPair.const_mul 2)) hE
  exact (congrArg (fun v:R3→ℝ=>∫ y,v y) hFun).trans
    (hOuter.trans (congrArg (fun v=>v+(∫ y,referenceDensityFamily g L (q,y)*‖e y‖^2)) hInner))


theorem exists_actual_full_model_error_with_exact_weighted_energy
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L q delta Rstar:ℝ) (p:ℕ)
    (cover:NativeNormalCover S L)
    (hCenter:∀ j:Fin cover.count,∀ z∈(cover.packet j).centers,‖z-(cover.packet j).y0‖ < (cover.packet j).rho)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:q∈Icc (0:ℝ) cover.dilationCeiling)
    (hRadius:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (K:Set R3) (F:smoothCompactFiniteSphereCore hO hD→R3→SphereL2)
    (hFData:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      ContDiff ℝ ∞ (F A) ∧ HasCompactSupport (F A) ∧ tsupport (F A)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F A y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y)
    (A:smoothCompactFiniteSphereCore hO hD) (hA:tsupport (A:R3→SphereL2)⊆K):
    ∃ E:R3→SphereL2,ContDiff ℝ ∞ E ∧ HasCompactSupport E ∧
      Integrable (fun y=>referenceDensityFamily S.g1 L (q,y)*‖E y‖^2) ∧
      (∀ y:R3,F A y=
        ((nativeNormalizedSecondReferenceModel hO hD hF S.g1 S.g2 S.g1_admissible L q delta Rstar p
          S.g2_admissible hd hRs A:R3→SphereL2) y)+E y) ∧
      ((∫ y,referenceDensityFamily S.g1 L (q,y)*‖F A y‖^2)=
        (∫ y,referenceDensityFamily S.g1 L (q,y)*‖((nativeNormalizedSecondReferenceModel hO hD hF S.g1 S.g2 S.g1_admissible L q delta Rstar p
          S.g2_admissible hd hRs A:R3→SphereL2) y)‖^2)+
        2*(∫ y,referenceDensityFamily S.g1 L (q,y)*inner ℝ ((nativeNormalizedSecondReferenceModel hO hD hF S.g1 S.g2 S.g1_admissible L q delta Rstar p
          S.g2_admissible hd hRs A:R3→SphereL2) y) (E y))+
        (∫ y,referenceDensityFamily S.g1 L (q,y)*‖E y‖^2)) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (E y))=
        nativePacketFinitePhysicalModelResidual hcalc hF hO hD tau0 S L cover q delta Rstar p A i y := by
  obtain ⟨E,hE,hEc,hEq,hGraph⟩:=exists_actual_full_model_error_field_with_explicit_residual_graph
    hcalc hreg hF hO hD tau0 S L q delta Rstar p cover hCenter hd hRs hLam hRadius K F hFData A hA
  let M:smoothCompactFiniteSphereCore hO hD:=
    nativeNormalizedSecondReferenceModel hO hD hF S.g1 S.g2 S.g1_admissible L q delta Rstar p
      S.g2_admissible hd hRs A
  have hInt:=referenceDensity_integrable_normSq_of_smooth_compact S.g1 S.g1_admissible L q E hE hEc
  have hEnergy:=referenceDensity_full_output_energy_eq_model_error_energy S.g1 S.g1_admissible L q
    (F A) (M:R3→SphereL2) E M.property.1 hE M.property.2.1 hEc hEq
  exact ⟨E,hE,hEc,hInt,hEq,hEnergy,hGraph⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
