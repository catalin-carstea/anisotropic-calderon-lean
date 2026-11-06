import Calderon.CompactMatrixEllipticity
import Calderon.WeightedMatrixCalculus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def coefficientSpatialBump : ContDiffBump (0 : R3) :=
  ⟨2,3,by norm_num,by norm_num⟩

def cutoffPrincipalCoefficient (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (p : P × R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  coefficientSpatialBump p.2 • matrixPrincipalCoefficient G p

def cutoffVolumeDensity (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (p : P × R3) : ℝ := coefficientSpatialBump p.2 * matrixVolumeDensity G p

theorem coefficientSpatialBump_eq_one (z : R3) (hz : ‖z‖ ≤ 1) :
    coefficientSpatialBump z = 1 := by
  apply coefficientSpatialBump.one_of_mem_closedBall
  simpa only [coefficientSpatialBump,mem_closedBall,dist_zero_right] using
    hz.trans (by norm_num : (1 : ℝ) ≤ 2)

theorem coefficientSpatialBump_eq_zero (z : R3) (hz : 3 ≤ ‖z‖) :
    coefficientSpatialBump z = 0 := by
  apply coefficientSpatialBump.zero_of_le_dist
  simpa only [coefficientSpatialBump,dist_zero_right] using hz

theorem cutoffPrincipalCoefficient_eq_on_unitBall
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : P × R3) (hz : ‖p.2‖ ≤ 1) :
    cutoffPrincipalCoefficient G p = matrixPrincipalCoefficient G p := by
  simp [cutoffPrincipalCoefficient,coefficientSpatialBump_eq_one p.2 hz]

theorem cutoffVolumeDensity_eq_on_unitBall
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : P × R3) (hz : ‖p.2‖ ≤ 1) :
    cutoffVolumeDensity G p = matrixVolumeDensity G p := by
  simp [cutoffVolumeDensity,coefficientSpatialBump_eq_one p.2 hz]

theorem contDiff_cutoffPrincipalCoefficient
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (hG : ContDiff ℝ ∞ G)
    (hpos : ∀ p, (G p).PosDef) : ContDiff ℝ ∞ (cutoffPrincipalCoefficient G) :=
  (coefficientSpatialBump.contDiff.comp contDiff_snd).smul
    (contDiff_matrixPrincipalCoefficient G hG hpos)

theorem contDiff_cutoffVolumeDensity
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (hG : ContDiff ℝ ∞ G)
    (hpos : ∀ p, (G p).PosDef) : ContDiff ℝ ∞ (cutoffVolumeDensity G) :=
  (coefficientSpatialBump.contDiff.comp contDiff_snd).mul
    (contDiff_matrixVolumeDensity G hG hpos)

theorem cutoffPrincipalCoefficient_eq_zero_outside
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : P × R3) (hz : 3 ≤ ‖p.2‖) :
    cutoffPrincipalCoefficient G p = 0 := by
  simp [cutoffPrincipalCoefficient,coefficientSpatialBump_eq_zero p.2 hz]

theorem cutoffVolumeDensity_eq_zero_outside
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : P × R3) (hz : 3 ≤ ‖p.2‖) :
    cutoffVolumeDensity G p = 0 := by
  simp [cutoffVolumeDensity,coefficientSpatialBump_eq_zero p.2 hz]

theorem exists_uniformlyElliptic_cutoffPrincipalCoefficient
    (G : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (hG : ContDiff ℝ ∞ G)
    (hpos : ∀ p, (G p).PosDef) (q : Set P) (hq : IsCompact q) :
    ∃ lam Lam : ℝ, ∀ p ∈ q,
      TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 1)
        (fun z => cutoffPrincipalCoefficient G (p,z)) lam Lam := by
  obtain ⟨lam,Lam,h⟩ := exists_compact_matrix_uniformlyElliptic
    (matrixPrincipalCoefficient G) (contDiff_matrixPrincipalCoefficient G hG hpos).continuous
    q hq (closedBall (0 : R3) 1) (isCompact_closedBall _ _)
    (fun p _ => matrixPrincipalCoefficient_posDef G hpos p)
  refine ⟨lam,Lam,fun p hp => (h p hp).congr ?_⟩
  intro z hz
  exact cutoffPrincipalCoefficient_eq_on_unitBall G (p,z)
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
end OAI.AnisotropicCalderon.MetricOperator
