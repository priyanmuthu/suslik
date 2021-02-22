package org.tygus.suslik.certification.targets.iris.logic

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions._
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HLocType, HType}
import org.tygus.suslik.certification.translation.{CardConstructor, GenericPredicate, GenericPredicateClause}
import org.tygus.suslik.language.{Ident, PrettyPrinting}

object Assertions {

  /** Unlike HTT, which encodes programs in a shallow embedding, Iris has a deep embedding of programs.
    * As such, program expressions are NOT Iris assertions (phi != HExpr). We define a lifting of
    * program-level expressions to spec-level. */
  abstract class IPureAssertion extends PrettyPrinting {
    def ppAsPhi: String = pp
  }

  abstract class IQuantifiedVar extends IPureAssertion

  abstract class ISpatialAssertion extends PrettyPrinting

  abstract class ISpecification extends PrettyPrinting

  case class ISpecLit(lit: HLit) extends IPureAssertion {
    override def pp: String = lit.pp
  }

  case class ISpecVar(name: String) extends IQuantifiedVar {
    override def pp: String = s"${name}"
  }

  case class ISpecQuantifiedValue(name: String) extends IQuantifiedVar {
    override def pp: String = s"${name}"
  }

  case class ISetLiteral(elems: List[IPureAssertion]) extends IPureAssertion {
    override def pp: String =
      s"([${elems.map(_.pp).mkString("; ")}] : list Z)"
  }

  case class ISpecUnaryExpr(op: HUnOp, expr: IPureAssertion) extends IPureAssertion {
    override def pp: String = s"${op.pp} ${expr.pp}"
  }

  case class ISpecBinaryExpr(op: HBinOp, left: IPureAssertion, right: IPureAssertion) extends IPureAssertion {
    override def pp: String = s"(${left.pp} ${op.pp} ${right.pp})"

    override def ppAsPhi: String = op match {
      case HOpLe | HOpLt => s"bool_decide (${left.pp} ${op.pp} ${right.pp})%Z"
      case HOpEq => s"bool_decide (${left.pp} ${op.pp} ${right.pp})"
      case _ => ???
    }
  }

  case class IAnd(conjuncts: Seq[IPureAssertion]) extends IPureAssertion {
    override def pp: String = s"${conjuncts.map(_.ppAsPhi).mkString(" ∧ ")}"
  }

  case class IPointsTo(loc: IPureAssertion, value: IPureAssertion) extends ISpatialAssertion {
    override def pp: String = s"${loc.pp} ↦ ${value.pp}"
  }

  case class IPredApp(pred: String, args: Seq[IPureAssertion], card: IPureAssertion) extends ISpatialAssertion {
    override def pp: String =
      s"(${pred} ${(args ++ List(card)).map(_.pp).mkString(" ")})"
  }

  case class IBlock() extends ISpatialAssertion {
    override def pp: String = s"⌜True⌝"
  }

  case class IHeap(heaplets: Seq[ISpatialAssertion]) extends ISpatialAssertion {
    override def pp: String = s"${heaplets.map(_.pp).mkString(" ∗ ")}"
  }

  case class IAssertion(phi: IPureAssertion, sigma: ISpatialAssertion) extends PrettyPrinting {
    override def pp: String = {
      val pure = if (phi.ppAsPhi.isEmpty) "" else s"⌜${phi.ppAsPhi}⌝"
      val spatial = sigma.pp
      val whole = s"${pure}${if(pure.nonEmpty && spatial.nonEmpty) " ∗ " else ""}${sigma.pp}"
      if (whole.isEmpty) "True" else whole
    }
  }

  case class IFunSpec(fname: String,
                      funArgs: Seq[(ISpecVar, HType)],
                      specUniversal: Seq[(IQuantifiedVar, HType)],
                      specExistential: Seq[(IQuantifiedVar, HType)],
                      pre: IAssertion,
                      post: IAssertion
                     ) extends ISpecification {

    override def pp: String = {
      // TODO: make this use the general translation mechanism
      def getArgLitVal(v: ISpecVar, t: HType): ISpecQuantifiedValue =
        (v, t) match {
          case (ISpecVar(name), HLocType()) => ISpecQuantifiedValue(s"l${name}")
          case (ISpecVar(name), _) => ISpecQuantifiedValue(s"v${name}")
        }

      val var_at = (v: ISpecVar, t: HType) => s"${t.pp}_at ${v.pp} ${getArgLitVal(v, t).pp}"
      val postExist =
        if (specExistential.nonEmpty)
          s"∃ ${specExistential.map({ case (v, ty) => s"(${v.pp} : ${ty.pp})"}).mkString(" ")}, "
        else ""

      s"""
         |Lemma ${fname}_spec :
         |∀ ${specUniversal.map({ case (v, ty) => s"(${v.pp} : ${ty.pp})"}).mkString(" ")},
         |${funArgs.map(v => var_at(v._1, v._2)).mkString(" →\n")} →
         |{{{ ${pre.pp} }}}
         |  ${fname} ${funArgs.map(v => v._1.pp).mkString(" ")}
         |{{{ RET #(); ${postExist}${post.pp} }}}.
         |""".stripMargin
    }
  }

  case class IPredicateClause(override val pure: List[IPureAssertion],
                              override val spatial: List[ISpatialAssertion],
                              override val subConstructor: Map[String, CardConstructor])
    extends GenericPredicateClause[IPureAssertion, ISpatialAssertion](pure, spatial, subConstructor)

  case class IPredicate(override val name: Ident,
                        override val params: List[(Ident, HType)],
                        override val existentials: List[(Ident, HType)],
                        override val clauses: Map[CardConstructor, IPredicateClause])
    extends GenericPredicate[IPureAssertion, ISpatialAssertion, HType](name, params, existentials, clauses) {

    def ppPredicate: String = {
      def ppConstructorClause(constr: CardConstructor, pclause: IPredicateClause): String = {
        val IPredicateClause(pure, spatial, _) = pclause
        val clause = IAssertion(IAnd(pure), IHeap(spatial))
        val ex = findExistentials(constr)(pclause)
        val exStr = if (ex.nonEmpty)  s"∃ ${ex.map({ case (name, ty) => s"($name : ${ty.pp})"}).mkString(" ")}, " else ""
        s"${exStr}${clause.pp}"
      }

      val predicate_definition =
        s"""Fixpoint ${name} ${params.map({ case (name, proofType) => s"(${name}: ${proofType.pp})" }).mkString(" ")} (self_card: ${inductiveName}) : iProp Σ := match self_card with
           ${
          clauses.map({ case (constructor, pclause@IPredicateClause(_, _, subConstructor)) =>
            s"|    | ${constructorName(constructor)} ${
              expandArgs(subConstructor)(constructor.constructorArgs)
            } => ${
              ppConstructorClause(constructor, pclause)
            }"
          }).mkString("\n")
        }
           |end.
           |""".stripMargin
      s"${predicate_definition}"
    }

    /**
      * For a given clause of the predicate and its associated constructor,
      * return the list of existential variables used in the body of the clause
      *
      * @param cons    a constructor matching some clause of the predicate
      * @param pclause the corresponding clause of the predicate
      * @return the list of pairs of (variable, variable_type) of all the existential variables in this clause
      * */
    override def findExistentials(cons: CardConstructor)(pclause: GenericPredicateClause[IPureAssertion, ISpatialAssertion]): List[(Ident, HType)] = {
      val paramMap = params.toMap

      //
      val existMap = existentials.toMap
      val cardMap = cons.constructorArgs

      pclause match {
        case IPredicateClause(pure, spatial, subClauses) =>
          val clauseCardMap = (cardMap ++ subClauses.flatMap({ case (_, cons) => cons.constructorArgs })).toSet

          def pureExistentials(exp: IPureAssertion): Set[Ident] = exp match {
            case ISpecVar(name) => {
              paramMap.get(name) match {
                // A variable that is neither (1) a parameter of the predicate nor (2) a cardinality IS an existential
                case None if !clauseCardMap.contains(name) => Set(name)
                case _ => Set()
              }
            }
            case ISpecBinaryExpr(_, left, right) => pureExistentials(left) ++ pureExistentials(right)
            case ISpecUnaryExpr(_, expr) => pureExistentials(expr)
            case ISetLiteral(elems) => elems.flatMap(pureExistentials).toSet
            case ISpecLit(_) => Set()
            case _ => ???
          }
          def spatialExistentials(heap: ISpatialAssertion): Set[Ident] = heap match {
            case IPointsTo(loc, value) => pureExistentials(loc) ++ pureExistentials(value)
            case IPredApp(_, args, _) => args.flatMap(pureExistentials).toSet
            case IHeap(heaplets) => heaplets.flatMap(spatialExistentials).toSet
            case IBlock() => Set()
            case _ => ???
          }
          (pure.flatMap(pureExistentials) ++ spatial.flatMap(spatialExistentials)).map(v => (v, existMap(v)))
      }
    }
  }

}