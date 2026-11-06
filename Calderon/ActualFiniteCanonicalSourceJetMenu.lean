import Calderon.ActualCanonicalSourceJetReconstruction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge DirichletFamily

theorem sum_abs_nine_column_lt_eighteen
    (A : Matrix (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) ℝ)
    (k : Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) (h : ∀ j, |A j k| < 2) :
    (∑ j, |A j k|) < 18 := by
  calc
    (∑ j, |A j k|) < ∑ _j : Fin 1 ⊕ (Fin 3 ⊕ Fin 5), (2 : ℝ) :=
      Finset.sum_lt_sum (fun j _ => (h j).le) ⟨Sum.inl 0, Finset.mem_univ _, h _⟩
    _ = 18 := by norm_num

theorem exists_finite_radiusTwoSourceJet_frame_cover
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ (T : Finset {p : R3 // p ∈ closedBall (0 : R3) 1})
      (f : T → (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ))
      (U : T → Set R3),
      closedBall (0 : R3) 1 ⊆ (⋃ p : T, U p) ∧
      ∀ p : T, IsOpen (U p) ∧ p.1.1 ∈ U p ∧
        U p ⊆ (radiusTwoOpens : Set R3) \ closedBall fixedExteriorSourceCenter (1/8 : ℝ) ∧
        radiusTwoSourceFreeJetMatrix g hg (f p) p.1.1 = 1 ∧
        ∀ q ∈ U p, (radiusTwoSourceFreeJetMatrix g hg (f p) q).det ≠ 0 ∧
          ∀ i j, |((radiusTwoSourceFreeJetMatrix g hg (f p) q)⁻¹) i j| < 2 := by
  classical
  have hEach (p : {p : R3 // p ∈ closedBall (0 : R3) 1}) :
      ∃ (f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ)) (U : Set R3),
        radiusTwoSourceFreeJetMatrix g hg f p.1 = 1 ∧ IsOpen U ∧ p.1 ∈ U ∧
        U ⊆ (radiusTwoOpens : Set R3) \ closedBall fixedExteriorSourceCenter (1/8 : ℝ) ∧
        ∀ q ∈ U, (radiusTwoSourceFreeJetMatrix g hg f q).det ≠ 0 ∧
          ∀ i j, |((radiusTwoSourceFreeJetMatrix g hg f q)⁻¹) i j| < 2 := by
    have hp : ‖p.1‖ ≤ 1 := mem_closedBall_zero_iff.mp p.2
    have hpB : p.1 ∈ (radiusTwoOpens : Set R3) := by
      change p.1 ∈ ball (0 : R3) 2
      exact mem_ball_zero_iff.mpr (by linarith)
    exact exists_radiusTwoSourceFreeJet_inverse_neighborhood g hg p.1 hpB
      (not_mem_fixedExteriorSource_closedBall_of_norm_le_one p.1 hp)
  choose f U hId hOpen hCenter hSub hInv using hEach
  have hCover : closedBall (0 : R3) 1 ⊆ ⋃ p : {p : R3 // p ∈ closedBall (0 : R3) 1}, U p := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, hCenter ⟨q, hq⟩⟩
  obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : R3) 1).elim_finite_subcover U hOpen hCover
  refine ⟨T, (fun p => f p.1), (fun p => U p.1), ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hT hq)
    obtain ⟨hpT, hqp⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨⟨p, hpT⟩, hqp⟩
  · intro p
    exact ⟨hOpen p.1, hCenter p.1, hSub p.1, hId p.1, hInv p.1⟩

theorem exists_finite_radiusTwoSource_canonicalJet_menu
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ (T : Finset {p : R3 // p ∈ closedBall (0 : R3) 1})
      (f : T → (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ)),
      ∀ q ∈ closedBall (0 : R3) 1,
        ∃ (p : T) (a : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → ℝ),
          (∀ k j, |a k j| < 2) ∧ (∀ k, (∑ j, |a k j|) < 18) ∧
          ∀ k, radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg q
              (∑ j, a k j • f p j) = compatibleSourceJetBasis g q k := by
  classical
  obtain ⟨T, f, U, hCover, hData⟩ := exists_finite_radiusTwoSourceJet_frame_cover g hg
  refine ⟨T, f, ?_⟩
  intro q hq
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hCover hq)
  obtain ⟨hOpen, hCenter, hSub, hId, hInv⟩ := hData p
  obtain ⟨hDet, hEntries⟩ := hInv q hp
  refine ⟨p, (fun k j => ((radiusTwoSourceFreeJetMatrix g hg (f p) q)⁻¹) j k), ?_, ?_, ?_⟩
  · intro k j
    exact hEntries j k
  · intro k
    exact sum_abs_nine_column_lt_eighteen _ k (fun j => hEntries j k)
  · intro k
    exact radiusTwoSmoothSourceJet_inverse_column g hg q (hSub hp).1 (hSub hp).2 (f p) hDet k

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
