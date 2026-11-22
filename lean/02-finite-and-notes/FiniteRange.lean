import Blocks.Segment00
import Blocks.Segment01
import Blocks.Segment02
import Blocks.Segment03
import Blocks.Segment04
import Blocks.Segment05
import Blocks.Segment06
import Blocks.Segment07
import Blocks.Segment08
import Blocks.Segment09
import Blocks.Segment10
import Blocks.Segment11
import Blocks.Segment12
import Blocks.Segment13
import Blocks.Segment14
import Blocks.Segment15
import Blocks.Low

namespace Goldbach.Finite
open Goldbach.Certificate

private theorem from923760 : Block true 923760 38121 :=
  @append true 923760 32768 5353 Segment14 Segment15

private theorem from858224 : Block true 858224 70889 :=
  @append true 858224 32768 38121 Segment13 from923760

private theorem from792688 : Block true 792688 103657 :=
  @append true 792688 32768 70889 Segment12 from858224

private theorem from727152 : Block true 727152 136425 :=
  @append true 727152 32768 103657 Segment11 from792688

private theorem from661616 : Block true 661616 169193 :=
  @append true 661616 32768 136425 Segment10 from727152

private theorem from596080 : Block true 596080 201961 :=
  @append true 596080 32768 169193 Segment09 from661616

private theorem from530544 : Block true 530544 234729 :=
  @append true 530544 32768 201961 Segment08 from596080

private theorem from465008 : Block true 465008 267497 :=
  @append true 465008 32768 234729 Segment07 from530544

private theorem from399472 : Block true 399472 300265 :=
  @append true 399472 32768 267497 Segment06 from465008

private theorem from333936 : Block true 333936 333033 :=
  @append true 333936 32768 300265 Segment05 from399472

private theorem from268400 : Block true 268400 365801 :=
  @append true 268400 32768 333033 Segment04 from333936

private theorem from202864 : Block true 202864 398569 :=
  @append true 202864 32768 365801 Segment03 from268400

private theorem from137328 : Block true 137328 431337 :=
  @append true 137328 32768 398569 Segment02 from202864

private theorem from71792 : Block true 71792 464105 :=
  @append true 71792 32768 431337 Segment01 from137328

private theorem from6256 : Block true 6256 496873 :=
  @append true 6256 32768 464105 Segment00 from71792

theorem balanced_6256_to_million (n : Nat) (lo : 6256 ≤ n)
    (hi : n ≤ 1000000) (even : n % 2 = 0) : BalancedFiltered n := by
  let i := (n-6256)/2
  have heq : n = 6256+2*i := by dsimp [i]; omega
  exact heq ▸ (from6256 i (by dsimp [i]; omega))

theorem goldbach_to_million (n : Nat) (lo : 4 ≤ n) (hi : n ≤ 1000000)
    (even : n % 2 = 0) : HasPair n := by
  by_cases h : 6256 ≤ n
  · exact (balanced_6256_to_million n h hi even).hasPair
  · let i := (n-4)/2
    have heq : n = 4+2*i := by dsimp [i]; omega
    exact heq ▸ (Low i (by dsimp [i]; omega))

end Goldbach.Finite
