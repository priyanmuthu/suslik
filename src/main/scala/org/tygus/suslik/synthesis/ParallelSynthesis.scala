package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.{Solution, _}
import org.tygus.suslik.report.{Log, ProofTrace}
import org.tygus.suslik.synthesis.tactics.Tactic
import org.tygus.suslik.util.SynStats

class ParallelSynthesis(tactic: Tactic, override implicit val log: Log, override implicit val trace: ProofTrace)
  extends Synthesis(tactic, log, trace) {

  protected override def runProcessWorkList(implicit stats: SynStats, config: SynConfig): Option[Solution] = {
    println(Console.RED + "ParallelSynthesis")
    super.runProcessWorkList(stats, config)
  }
}