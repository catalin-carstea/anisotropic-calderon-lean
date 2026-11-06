import Calderon.ActualFiniteFixedSourceWitnesses
import Calderon.ActualFixedSourceValueJet
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace Filter
open scoped ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge DirichletFamily Literature MetricVolume MetricCompatibleSourceJetAlgebra

def rawJetFreeCoordinates (J : RadiusTwoRawTwoJet) :
    (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → ℝ :=
  Sum.elim (fun _ => J.1) (Sum.elim
    (fun i => J.2.1 (coordinateVector i))
    (fun k => ![J.2.2 (coordinateVector 0) (coordinateVector 0),
      J.2.2 (coordinateVector 1) (coordinateVector 1),
      J.2.2 (coordinateVector 0) (coordinateVector 1),
      J.2.2 (coordinateVector 0) (coordinateVector 2),
      J.2.2 (coordinateVector 1) (coordinateVector 2)] k))

def compatibleSourceJetBasis (g : MatrixField) (p : R3) :
    (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → RadiusTwoRawTwoJet :=
  Sum.elim (fun _ => (1, (0, 0))) (Sum.elim
    (fun i => (0, (EuclideanSpace.proj i,
      matrixJetBilinear (gradientCorrectionHessianMatrix g p (EuclideanSpace.proj i)))))
    (fun k => (0, (0, matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k)))))

theorem rawJetFreeCoordinates_compatibleSourceJetBasis
    (g : MatrixField) (p : R3) (i j : Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) :
    rawJetFreeCoordinates (compatibleSourceJetBasis g p j) i = if i = j then 1 else 0 := by
  classical
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    fin_cases i <;> fin_cases j <;>
    simp only [rawJetFreeCoordinates, compatibleSourceJetBasis,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_fin_one, matrixJetBilinear_coordinateVector] <;>
    simp [gradientCorrectionHessianMatrix, traceFreeHessianMatrix,
      coordinateMatrixUnit, EuclideanSpace.coe_proj, coordinateVector, PiLp.single_apply]

theorem exists_radiusTwoSmoothSourceJet_basis
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ),
      ∀ j, radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p (f j) =
        compatibleSourceJetBasis g p j := by
  classical
  obtain ⟨f0, hf0⟩ := FixedSourceWitnesses.exists_radiusTwoSmoothSource_unitValue_zeroDerivatives
    g hg p hp hSource
  obtain ⟨fG, hfG⟩ := FixedSourceWitnesses.exists_radiusTwoSmoothSource_coordinate_firstJets
    g hg p hp hSource
  obtain ⟨fH, hfH⟩ := FixedSourceWitnesses.exists_radiusTwoSmoothSource_zeroGradient_fiveHessians
    g hg p hp hSource
  refine ⟨Sum.elim (fun _ => f0) (Sum.elim fG fH), ?_⟩
  intro j
  rcases j with j | (j | j)
  · exact Prod.ext hf0.1 (Prod.ext hf0.2.1 hf0.2.2)
  · exact Prod.ext (hfG j).1 (Prod.ext (hfG j).2.1 (hfG j).2.2)
  · exact Prod.ext (hfH j).1 (Prod.ext (hfH j).2.1 (hfH j).2.2)

def radiusTwoSourceFreeJetMatrix
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ)) (x : R3) :
    Matrix (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) ℝ :=
  fun i j => rawJetFreeCoordinates
    (radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg x (f j)) i

theorem continuousAt_radiusTwoSourceFreeJetMatrix
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    ContinuousAt (radiusTwoSourceFreeJetMatrix g hg f) p := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have h0 := (radiusTwoSmoothSourceResponse_spec
    fixedDirichletRegularity fixedSobolevCalculus g hg (f j)).2.1
  have h1 : ContDiffOn ℝ ∞
      (fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f j)))
      (radiusTwoOpens : Set R3) :=
    h0.fderiv_of_isOpen radiusTwoOpens.isOpen (by simp)
  have h2 : ContDiffOn ℝ ∞
      (fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f j))))
      (radiusTwoOpens : Set R3) :=
    h1.fderiv_of_isOpen radiusTwoOpens.isOpen (by simp)
  have hn := radiusTwoOpens.isOpen.mem_nhds hp
  rcases i with i | (i | i)
  · exact (h0.contDiffAt hn).continuousAt
  · exact (h1.contDiffAt hn).continuousAt.clm_apply continuousAt_const
  · fin_cases i <;>
      exact ((h2.contDiffAt hn).continuousAt.clm_apply continuousAt_const).clm_apply continuousAt_const

theorem exists_radiusTwoSourceFreeJetMatrix_eq_one
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSourceFreeJetMatrix g hg f p = 1 := by
  obtain ⟨f, hf⟩ := exists_radiusTwoSmoothSourceJet_basis g hg p hp hSource
  refine ⟨f, ?_⟩
  ext i j
  change rawJetFreeCoordinates
    (radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg p (f j)) i = _
  rw [hf j]
  exact rawJetFreeCoordinates_compatibleSourceJetBasis g p i j

theorem exists_matrix_inverse_entry_neighborhood
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : R3 → Matrix ι ι ℝ) (p : R3)
    (hCont : ContinuousAt M p) (hM : M p = 1) :
    ∃ U : Set R3, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U,
      (M x).det ≠ 0 ∧ ∀ i j, |((M x)⁻¹) i j| < 2 := by
  have hDet : (M p).det ≠ 0 := by rw [hM, Matrix.det_one]; exact one_ne_zero
  have hRI : ContinuousAt (Ring.inverse : ℝ → ℝ) (M p).det := by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hDet)
  have hInv : ContinuousAt (fun x => (M x)⁻¹) p :=
    (continuousAt_matrix_inv (M p) hRI).comp hCont
  have hDetCont : ContinuousAt (fun x => (M x).det) p :=
    continuous_id.matrix_det.continuousAt.comp hCont
  have hDetNear : ∀ᶠ x in 𝓝 p, (M x).det ≠ 0 := hDetCont.eventually_ne hDet
  have hEach (i j : ι) : ∀ᶠ x in 𝓝 p, |((M x)⁻¹) i j| < 2 := by
    have he : ContinuousAt (fun x => ((M x)⁻¹) i j) p :=
      (continuous_apply j).continuousAt.comp
        ((continuous_apply i).continuousAt.comp hInv)
    have hlt : |((M p)⁻¹) i j| < (2 : ℝ) := by
      rw [hM, inv_one]
      by_cases h : i = j <;> norm_num [Matrix.one_apply, h]
    exact he.abs.eventually_lt continuousAt_const hlt
  have hAll : ∀ᶠ x in 𝓝 p, ∀ i j, |((M x)⁻¹) i j| < 2 :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hEach i)
  obtain ⟨U, hUsub, hU, hpU⟩ := _root_.mem_nhds_iff.mp (hDetNear.and hAll)
  exact ⟨U, hU, hpU, fun x hx => hUsub hx⟩

theorem exists_radiusTwoSourceFreeJet_inverse_neighborhood
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ (f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ)) (U : Set R3),
      radiusTwoSourceFreeJetMatrix g hg f p = 1 ∧
      IsOpen U ∧ p ∈ U ∧ U ⊆ (radiusTwoOpens : Set R3) \ closedBall fixedExteriorSourceCenter (1/8 : ℝ) ∧
      ∀ x ∈ U, (radiusTwoSourceFreeJetMatrix g hg f x).det ≠ 0 ∧
        ∀ i j, |((radiusTwoSourceFreeJetMatrix g hg f x)⁻¹) i j| < 2 := by
  obtain ⟨f, hf⟩ := exists_radiusTwoSourceFreeJetMatrix_eq_one g hg p hp hSource
  obtain ⟨U, hU, hpU, hUprop⟩ := exists_matrix_inverse_entry_neighborhood
    (radiusTwoSourceFreeJetMatrix g hg f) p (continuousAt_radiusTwoSourceFreeJetMatrix g hg f p hp) hf
  have hBall : IsOpen (radiusTwoOpens : Set R3) :=
    (show IsOpen (ball (0 : R3) 2) from isOpen_ball)
  refine ⟨f, U ∩ ((radiusTwoOpens : Set R3) \ closedBall fixedExteriorSourceCenter (1/8 : ℝ)), hf,
    _root_.IsOpen.inter hU (_root_.IsOpen.sdiff hBall isClosed_closedBall), ⟨hpU, hp, hSource⟩,
    fun x hx => hx.2, fun x hx => hUprop x hx.1⟩

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
