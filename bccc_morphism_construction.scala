/* Generator of canonical morphisms in bicartesian closed categories.
 *
 * This script contains a Scala implementation of a little embedded
 * domain-specific language that can build canonical morphisms
 * in BCCC's using only domain and codomain types as hints.
 *
 * For example, this framework can take the following, human readable
 * chain of hom-set descriptions
 *
 *   (Hom(D, Exp(C, A)) x Hom(D, Exp(C, B)) x Hom(D, A U B)) ~
 *   (Hom(D x A, C) x Hom(D x B, C) x Hom(D, A U B)) ~
 *   (Hom(A x D, C) x Hom(B x D, C) x Hom(D, A U B)) ~
 *   (Hom(A, Exp(C, D)) x Hom(B, Exp(C, D)) x Hom(D, A U B)) ~
 *   (Hom(A U B, Exp(C, D)) x Hom(D, A U B)) ~
 *   (Hom((A U B) x D, C) x Hom(D, A U B)) ~
 *   (Hom(D x (A U B), C) x Hom(D, A U B)) ~
 *   (Hom(D, Exp(C, A U B)) x Hom(D, A U B)) ~
 *   Hom(D, Exp(C, A U B) x (A U B)) 
 *
 * and generate the following (rather incomprehensible) explicit 
 * isomorphism out of it:
 *
 *   (a, b, f) => 
 *     <λ(ε o <[λ(ε o <a o π_1,π_2> o <π_2,π_1>),
 *      λ(ε o <b o π_1,π_2> o <π_2,π_1>)] o π_1,π_2> o <π_2,π_1>),f>
 *
 * Can also be used to extract isomorphisms between objects from isomorphism 
 * between hom sets (application of the Yoneda-lemma).
 *
 * @author: Andrey Tyukin
 * @date: 2015-12-23
 * 
 */

/*##############################################################################
      Bicartesian closed categories, basic building blocks 
##############################################################################*/
sealed trait Obj {
  def toTex: String
  def toCode: String
  def x(other: Obj) = Prod(this, other)
  def U(other: Obj) = Coprod(this, other)
  def ^(other: Obj) = Exp(this, other)
}

case class AtomObj(name: String) extends Obj {
  override def toString = name
  def toTex = name
  def toCode = name
}

case object Terminal extends Obj {
  override def toString = "T"
  def toTex = """\mathbb{T}"""
  def toCode = """Terminal"""
}

case object Initial extends Obj {
  override def toString = "I"
  def toTex = """\mathbb{I}"""
  def toCode = "Initial"
}

case class Exp(cod: Obj, dom: Obj) extends Obj {
  override def toString = "(%s^%s)".format(cod, dom)
  def toTex = " ({ %s}^{ %s}) ".format(cod.toTex, dom.toTex)
  def toCode = "Exp[%s,%s]".format(cod.toCode, dom.toCode)
}

case class Prod(a: Obj, b: Obj) extends Obj {
  override def toString = "(%s x %s)".format(a, b)
  def toTex = """ ({ %s}\times{ %s}) """.format(a.toTex, b.toTex)
  def toCode = "Prod[%s,%s]".format(a.toCode, b.toCode)
}

case class Coprod(a: Obj, b: Obj) extends Obj {
  override def toString = "(%s U %s)".format(a, b)
  def toTex = """ ({ %s}\amalg{ %s}) """.format(a.toTex, b.toTex)
  def toCode = "Coprod[%s,%s]".format(a.toCode, b.toCode)
}

sealed trait Mor {
  def toTex: String
  def toCode: String
  def dom: Obj
  def cod: Obj
  def scalaTypeString = "Hom[%s,%s]".format(dom.toCode, cod.toCode)
  def o (other: Mor): Mor = Comp(this, other)
}

case class Id(dom: Obj) extends Mor {
  def cod = dom
  override def toString = "Id_%s".format(dom)
  def toTex = """\textrm{Id}_{ %s}""".format(dom.toTex)
  def toCode = "Id[%s]".format(dom.toCode)
}

case class Comp(second: Mor, first: Mor) extends Mor {
  require(first.cod == second.dom,
    "first  = " + first + "\n" + 
    "second = " + second + "\n" +
    "first.cod = " + first.cod + "\n" +
    "second.dom = " + second.dom
  )
  def dom = first.dom
  def cod = second.cod
  override def toString = "%s o %s".format(second, first)
  def toTex = """ %s\circ %s """.format(second.toTex, first.toTex)
  def toCode = "(\n%s o \n%s)".format(second.toCode, first.toCode)
}

case class InitMor(cod: Obj) extends Mor {
  def dom = Initial
  override def toString = "!_%s".format(cod)
  def toTex = "!_{ %s}".format(cod.toTex)
  def toCode = "InitMor[%s]".format(cod.toCode)
}

case class TermMor(dom: Obj) extends Mor {
  def cod = Terminal
  override def toString = "\u2020_%s".format(dom)
  def toTex = """\dagger_{ %s}""".format(dom.toTex)
  def toCode = "TermMor[%s]".format(dom.toCode)
}

case class ProdMor(f: Mor, g: Mor) extends Mor {
  require(f.dom == g.dom)
  def dom = f.dom
  def cod = Prod(f.cod, g.cod)
  override def toString = "<%s,%s>".format(f, g)
  def toTex = """\langle %s,%s\rangle""".format(f.toTex, g.toTex)
  def toCode = "ProdMor(%s,%s)".format(f.toCode, g.toCode)
}

case class P1(a: Obj, b: Obj) extends Mor {
  def dom = Prod(a, b)
  def cod = a
  override def toString = "\u03c0_1"
  def toTex = """\pi_1^{ %s, %s}""".format(a.toTex, b.toTex)
  def toCode = """P1[%s, %s]""".format(a.toCode, b.toCode)
}

case class P2(a: Obj, b: Obj) extends Mor {
  def dom = Prod(a, b)
  def cod = b
  override def toString = "\u03c0_2"
  def toTex = """\pi_2^{ %s, %s}""".format(a.toTex, b.toTex)
  def toCode = """P2[%s, %s]""".format(a.toCode, b.toCode)
}

case class I1(a: Obj, b: Obj) extends Mor {
  def dom = a
  def cod = Coprod(a, b)
  override def toString = "\u0399_1"
  def toTex = """\iota_1^{ %s, %s}""".format(a.toTex, b.toTex)
  def toCode = """I1[%s, %s]""".format(a.toCode, b.toCode)
}

case class I2(a: Obj, b: Obj) extends Mor {
  def dom = b
  def cod = Coprod(a, b)
  override def toString = "\u0399_2"
  def toTex = """\iota_2^{ %s, %s}""".format(a.toTex, b.toTex)
  def toCode = """I2[%s, %s]""".format(a.toCode, b.toCode)
}

case class CoprodMor(f: Mor, g: Mor) extends Mor {
  require(f.cod == g.cod)
  def dom = Coprod(f.dom, g.dom)
  def cod = f.cod
  override def toString = "[%s,%s]".format(f, g)
  def toTex = """[%s,%s]""".format(f.toTex, g.toTex)
  def toCode = "CoprodMor(%s, %s)".format(f.toCode, g.toCode)
}

case class Lambda(f: Mor) extends Mor {
  require(f.dom match {
    case Prod(_, _) => true
    case _ => false
  }, "Cannot abstract %s, domain is %s (not a product)".format(f, f.dom) )
  private val f_domain_components = { val Prod(a, b) = f.dom; (a, b) }
  def dom = f_domain_components._1
  def cod = Exp(f.cod, f_domain_components._2)
  override def toString = "\u03bb(%s)".format(f)
  def toTex = """\lambda( %s )""".format(
    // f_domain_components._1.toTex,
    // f_domain_components._2.toTex,
    // f.cod.toTex,
    f.toTex
  )
  def toCode = """Lambda[%s,%s,%s](%s)""".format(
    f_domain_components._1.toCode,
    f_domain_components._2.toCode,
    f.cod.toCode,
    f.toCode
  )
}

case class Eval(in: Obj, cod: Obj) extends Mor {
  def dom = Prod(Exp(cod, in), in)
  override def toString = "\u03b5"
  def toTex = """\varepsilon^{ %s,%s}""".format(in.toTex, cod.toTex)
  def toCode = """Eval[%s,%s]""".format(in.toCode, cod.toCode)
}

case class VariableMor(name: String, dom: Obj, cod: Obj) extends Mor {
  def toTex = name
  def toCode = name
  override def toString = name
}

/*##############################################################################
                       Additional useful morphism constructors 
##############################################################################*/
def times(f: Mor, g: Mor): Mor = {
  ProdMor(f o P1(f.dom, g.dom), g o P2(f.dom, g.dom))
}

def amalg(f: Mor, g: Mor): Mor = {
  CoprodMor(I1(f.cod, g.cod) o f, I2(f.cod, g.cod) o g)
}

/*##############################################################################
                            Some useful isomorphisms
##############################################################################*/

/** A x B ~ B x A */
def swapProd(a: Obj, b: Obj): Mor = ProdMor(P2(a, b), P1(a, b))

/** Hom[X, A x B] ~ Hom[X, A] x Hom[X, B] (inverse to <-,->) */
def splitProd(fg: Mor): (Mor, Mor) = fg.cod match {
  case Prod(a, b) => (P1(a, b) o fg, P2(a, b) o fg)
  case _ => throw new Exception("Cannot split morphism as <f,g>: " + fg)
}

/** A + B ~ B + A */
def swapCoprod(a: Obj, b: Obj): Mor = CoprodMor(I2(a, b), I1(a, b))

/** Hom[A + B, X] ~ Hom[A, X] x Hom[B, X] (inverse to [-,-]) */
def splitCoprod(fg: Mor): (Mor, Mor) = fg.dom match {
  case Coprod(a, b) => (fg o I1(a, b), fg o I2(a, b))
  case _ => throw new Exception("Cannot split as [f, g]: " + fg)
}

/** Hom[X, Z^Y] ~ Hom[X x Y, Z] (inverse to lambda) */
def uncurry(f: Mor): Mor = f.cod match {
  case Exp(z, y) => {
    Eval(y, z) o times(f, Id(y))
  }
  case _ => {
    throw new Exception("Cannot uncurry a morphism, cod not exponential: " + f)
  }
}

/** A ~ T x A (add/remove terminal object from left) */
def addTerminalLeft(a: Obj): Mor = ProdMor(TermMor(a), Id(a))
def removeTerminalLeft(a: Obj): Mor = P2(Terminal, a)

/** A ~ A x T (add/remove terminal object from right) */
def addTerminalRight(a: Obj): Mor = ProdMor(Id(a), TermMor(a))
def removeTerminalRight(a: Obj): Mor = P1(a, Terminal)

/*##############################################################################
                            Variable arrow elimination
##############################################################################*/

def s(xaz: Mor, xzb: Mor): Mor = { 
  // extract objects from domains/codomains of inputs
  val x = xaz.dom
  val Exp(z,a) = xaz.cod
  val Exp(b,w) = xzb.cod
  require(z == w)
  // build the X -> B^A morphism
  Lambda(Eval(z, b) o ProdMor(xzb o P1(x, a), uncurry(xzb)))
}

def k(x: Obj, c: Mor): Mor = {
  val a = c.dom
  Lambda(c o P2(Terminal, a)) o TermMor(x)
}

def i(x: Mor): Mor = { 
  val xo = x.cod
  Lambda(P1(xo, Terminal))
}

def abstractProd(xab1: Mor, xab2: Mor): Mor = {
  Lambda(ProdMor(uncurry(xab1), uncurry(xab2)))
}

def abstractCoprod(xa1b: Mor, xa2b: Mor): Mor = {
  ???
}

/** 
 * Eliminates an arrow `x: T -> X` from a morphism `f: A -> B`, yielding a 
 * morphism `E_x(f): X -> B^A` such that for each `a: T -> A` it holds:
 * `eval o < E_x(f) o x, a> = f o a`.
 */
def abstractVar(x: VariableMor, f: Mor): Mor = f match {
  case Comp(a, b) => s(abstractVar(x, a), abstractVar(x, b))
  case v: VariableMor if (v == x) => i(x)
  case ProdMor(f, g) => abstractProd(abstractVar(x, f), abstractVar(x, g))
  case CoprodMor(f, g) => abstractCoprod(abstractVar(x, f), abstractVar(x, g))
  case c => k(x.cod, c)
}

/*##############################################################################
                                      Utils
##############################################################################*/
// Bag of stuff...
def sequence[X](list: List[Option[X]]): Option[List[X]] = {
  list match {
    case Nil => Some(Nil)
    case h :: t => for (hVal <- h; tail <- sequence(t)) yield (hVal :: tail)
  }
}

/** Finds a permutation such that `b = a o pi`, if uniquely possible.
 */
def extractPermutation[A](a: List[A], b: List[A]): Option[Vector[Int]] = {
  val aSet = a.toSet
  val bSet = b.toSet
  if (aSet != bSet) {
    None
  } else if (aSet.size != a.size || bSet.size != b.size) {
    None
  } else {
    val a_inv = (a zip Stream.from(0)).toMap
    Some((b map a_inv).toVector)
  }
}

/** 
  * Generates all possible "partitions ~ tokenizations" of a list,
  * e.g. a list of 6 elements can be cut into 4 parts in the following ways:
  *
  *       *|*|*|***
  *       *|*|**|**
  *       *|*|***|*
  *       *|**|*|**
  *       *|**|**|*
  *       *|***|*|*
  *       **|*|*|**
  *       **|*|**|*
  *       **|**|*|*
  *       ***|*|*|*
  */
def linearPartitions[A](k: Int, l: List[A]): List[List[List[A]]] = {
  if (k == 1) List(List(l))
  else {
    for (
      f <- (1 to (l.size - k + 1)).toList;
      p <- linearPartitions(k - 1, l.drop(f))
    ) yield (l.take(f) :: p)
  }
}

/**
  * Returns some `List[Y]` only if every `x` in `xs` is mapped to some
  * element of type `Y`. Does not try to find solutions for elements in
  * the tail as soon as `f(x)` fails for at least one `x`.
  */
def findAll[X, Y](xs: List[X])(f: X => Option[Y]): Option[List[Y]] = { 
  xs match {
    case Nil => Some(Nil)
    case h :: t => for (
      hSolution <- f(h);
      tSolutions <- findAll(t)(f)
    ) yield hSolution :: tSolutions
  }
}

/**
  * Tries `xs` sequentially until the first `Some[Y]` is produced.
  * Returns `Some[Y]` as soon as `f(x)` succeeds for the first time.
  */
def findSome[X, Y](xs: List[X])(f: X => Option[Y]): Option[Y] = {
  xs match {
    case Nil => None
    case x :: tail => f(x) match {
      case Some(y) => Some(y)
      case None => findSome(tail)(f)
    }
  }
}

/*##############################################################################
                      Mappings between (products of) hom-sets
##############################################################################*/
case class Hom(dom: Obj, cod: Obj) {
  def x(other: Hom) = HomProd(List(this, other))
  def substitute(s: Map[String, Obj]) = Hom(substObj(s, dom), substObj(s, cod))
  def toTex = "\\textrm{Hom}[%s,%s]".format(dom.toTex, cod.toTex)
}

case class HomProd(factors: List[Hom]) {
  def x (oneMore: Hom) = HomProd(factors ++ List(oneMore))
  def substitute(s: Map[String, Obj]) = HomProd(factors.map{_.substitute(s)})
  override def toString = factors.mkString(" x ")
  def toTex = factors.map{_.toTex}.mkString(" \\times ")
}

/**
  * Convert stand-alone Hom-sets into "unary products"
  */
import scala.language.implicitConversions
implicit def unaryHomProd(hom: Hom): HomProd = HomProd(List(hom))
implicit def homProd2homSeq(hp: HomProd): HomSeq = HomSeq(List(hp), Nil)
implicit def hom2homSeq(h: Hom): HomSeq = HomSeq(List(h), Nil)

/**
  * A mapping between things like 
  * `Hom[A_1, B_1] x ... x Hom[A_n, B_n]`.
  * It can be interpreted as morphism, or as a natural transformation,
  * depending on how many objects one sees as 'fixed', and how many as 
  * 'variable'.
  */
trait HomMapping {
  def dom: HomProd
  def cod: HomProd
  /**
    * Checks whether arguments match the domain.
    * Throws errors if not.
    */
  def check(arg: List[Mor]): Unit = {
    require(arg.size == dom.factors.size, 
      "#args = %s != %s = #factors".format(arg.size, dom.factors.size)
    )
    for ((a, Hom(d, c)) <- arg zip dom.factors) {
      require(a.dom == d, "Wrong domain: " + a.dom + " <-> " + d + " for\n " +
        "HomMapping: " + this + " \n " + 
        "Morphism: " + a
      )
      require(a.cod == c, "Wrong codomain: " + a.cod + " <-> " + c + " for\n " +
        "HomMapping: " + this + " \n " + 
        "Morphism: " + a
      )
    }
  }
  /**
    * Raw version of `apply` that does not perform any type-checks
    */
  protected def _apply(args: List[Mor]): List[Mor] 
  def apply(args: List[Mor]): List[Mor] = { check(args); _apply(args) }
  def substitute(s: Map[String, Obj]): HomMapping
  def inverse: Option[HomMapping]
  def isInvertible = !inverse.isEmpty
  /** single-line, no break, no arrow, only representation of this mapping */
  def toTex: String
}

/**
  * Composition of hom-mappings (apply first, then second, then third, etc...)
  */
case class HomMappingComposition(parts: List[HomMapping]) 
extends HomMapping {
  def dom = parts.head.dom
  def cod = parts.last.cod
  protected def _apply(arg: List[Mor]): List[Mor] = { 
    parts.foldLeft(arg){ case (mors, map) => map(mors) }
  }
  def substitute(s: Map[String, Obj]): HomMappingComposition = { 
    HomMappingComposition(parts.map(_.substitute(s)))
  }
  def inverse: Option[HomMapping] = { 
    for (inverses <- sequence(parts.map(_.inverse))) 
    yield HomMappingComposition(inverses.reverse)
  }
  override def toString = parts.mkString(
    "HomMappingComposition(\n  ", 
    ",\n  ",
    "\n)"
  )
  def toTex = throw new UnsupportedOperationException("never used")
  def toDiagram(drawInverses: Boolean) = {
    val bldr = new StringBuilder
    for (p <- parts) {
      bldr ++= p.dom.toTex
      bldr ++= "\\\\\n"
      bldr ++= "\\dTo^{ %s} ".format(p.toTex)
      if (drawInverses) {
        for (inv <- p.inverse) {
          bldr ++= "\\uTo_{ %s}".format(inv.toTex)
        }
      }
      bldr ++= "\\\\\n"
    }
    bldr ++= parts.last.cod.toTex
    bldr.toString
  }
}

/**
  * A mapping that simply permutates the hom-sets.
  * E.g. `Hom[A, B] x Hom[C, D] x Hom[E, F]` can be 
  * transformed to `Hom[C, D] x Hom[E, F] x Hom[A, B]` with
  * the permutation `pi = [1, 2, 0]`.
  */
case class PermutationHomMapping(
  permutation: Vector[Int], /* 0-based */
  homs: Vector[Hom] 
) extends HomMapping {
  val dom = HomProd(homs.toList)
  val cod = HomProd(permutation.map{i => homs(i)}.toList)
  protected def _apply(args: List[Mor]): List[Mor] = {
    val vargs = args.toVector
    permutation.toList.map{i => vargs(i)}
  }
  def substitute(s: Map[String, Obj]): PermutationHomMapping = {
    PermutationHomMapping(permutation, homs.map{_.substitute(s)})
  }
  def inverse = {
    val p_inv = 
      (0 until permutation.size).
      map{i => (i, permutation(i))}.
      sortBy(_._2).
      map{_._1}.
      toVector
    Some(PermutationHomMapping(p_inv, cod.factors.toVector))
  }
  def toTex = {
    val p_inv = 
      (0 until permutation.size).
      map{i => (i, permutation(i))}.
      sortBy(_._2).
      map{_._1}.
      toVector
    permutation.mkString("(", ",",")")
  }
}

/**
  * List of hom-mappings that operate in parallel.
  * E.g. if `f: Hom[A, C] x Hom[B, C] -> Hom[A x B, C]` and
  * `g: Hom[X, Y] -> Hom[Z, W]`, then their cross product 
  * will be a hom-mapping from `Hom[A, C] x Hom[B, C] x Hom[X, Y]` to
  * `Hom[A x B, C] x Hom[Z, W]`.
  */
case class CrossProdOfHomMappings(ms: List[HomMapping])
extends HomMapping {
  def dom = HomProd(ms.flatMap{_.dom.factors})
  def cod = HomProd(ms.flatMap{_.cod.factors})
  protected def _apply(args: List[Mor]): List[Mor] = {
    var remainingArgs = args
    var reverseResults: List[Mor] = Nil
    for (m <- ms) {
      val mArgs = remainingArgs.take(m.dom.factors.size)
      remainingArgs = remainingArgs.drop(m.dom.factors.size)
      val mResults = m(mArgs)
      reverseResults = mResults.reverse ++ reverseResults
    }
    val results = reverseResults.reverse
    results
  }
  def substitute(s: Map[String, Obj]): HomMapping = 
    CrossProdOfHomMappings(ms.map{_.substitute(s)})
  def inverse: Option[HomMapping] = {
    for (inverses <- sequence(ms.map{_.inverse})) yield {
      CrossProdOfHomMappings(inverses)
    }
  }
  override def toString = ms.mkString(" x ")
  def toTex = {
    if (ms.size > 1) ms.map{
      x => "(" + x.toTex + ")"
    }.mkString(" \\times ")
    else ms.map{_.toTex}.mkString(" \\times ")
  }
}

/**
  * If `f: C -> A` and `g: B -> D`, then `Hom[f, g] : Hom[A, B] -> Hom[C, D]`.
  * It simply pre- and post-composes `f` and `g` to morphisms from `Hom[A, B]`.
  */
case class HomBifunctor(
  pre: Mor, pre_inv: Option[Mor],
  post: Mor, post_inv: Option[Mor]
) extends HomMapping {
  def dom = Hom(pre.cod, post.dom)
  def cod = Hom(pre.dom, post.cod)
  protected def _apply(arg: List[Mor]) = List(post o arg.head o pre)
  def substitute(s: Map[String, Obj]) = 
    HomBifunctor(
      substMor(s, pre),
      pre_inv.map{ f => substMor(s, f) },
      substMor(s, post),
      post_inv.map{ f => substMor(s, f) }
    )
  def inverse = 
    for (pri <- pre_inv; poi <- post_inv) 
    yield HomBifunctor(pri, Some(pre), poi, Some(post))
  override def toString = "Hom(%s,%s)".format(pre, post)
  def toTex = {
    (pre, post) match {
      case (Id(_), Id(_)) => "\\textrm{Id}"
      case (Id(_), f) => f.toTex + " \\circ -"
      case (f, Id(_)) => "- \\circ " + f.toTex
      case (f, g) => "\\textrm{Hom}[%s,%s]".format(f.toTex, g.toTex)
    }
  }
}

/*##############################################################################
            Bunch of hom-set-mappings that can be used as patterns
##############################################################################*/

case class Prod_UnivProp_mediating(Z: Obj, A: Obj, B: Obj) extends HomMapping {
  def dom = Hom(Z, A) x Hom(Z, B)
  def cod = Hom(Z, A x B)
  protected def _apply(arg: List[Mor]): List[Mor] = {
    val f = arg(0)
    val g = arg(1)
    List(ProdMor(f, g))
  }
  def substitute(s: Map[String, Obj]): HomMapping = Prod_UnivProp_mediating(
    substObj(s, Z), 
    substObj(s, A), 
    substObj(s, B)
  )
  def inverse: Option[HomMapping] = Some(Prod_UnivProp_split(Z, A, B))
  def toTex ="\\langle -, - \\rangle"
}

case class Prod_UnivProp_split(Z: Obj, A: Obj, B: Obj) extends HomMapping {
  def dom = Hom(Z, A x B)
  def cod = Hom(Z, A) x Hom(Z, B)
  protected def _apply(arg: List[Mor]): List[Mor] = {
    val fg = arg.head
    List(P1(A, B) o fg, P2(A, B) o fg)
  }
  def substitute(s: Map[String, Obj]) = Prod_UnivProp_split(
    substObj(s, Z),
    substObj(s, A),
    substObj(s, B)
  )
  def inverse: Option[HomMapping] = Some(Prod_UnivProp_mediating(Z, A, B))
  def toTex = {
    "(\\pi_1^{ %1$s,%2$s} \\circ -, \\pi_2^{ %1$s,%2$s} \\circ -)".
    format(A.toTex, B.toTex)
  }
}

case class Coprod_UnivProp_mediating(A: Obj, B: Obj, Z: Obj) 
extends HomMapping {
  def dom = Hom(A, Z) x Hom(B, Z)
  def cod = Hom(A U B, Z)
  protected def _apply(arg: List[Mor]): List[Mor] = {
    val f = arg(0)
    val g = arg(1)
    List(CoprodMor(f, g))
  }
  def substitute(s: Map[String, Obj]): HomMapping = Coprod_UnivProp_mediating(
    substObj(s, A),
    substObj(s, B),
    substObj(s, Z)
  )
  def inverse = Some(Coprod_UnivProp_split(A, B, Z))
  def toTex = "[-, -]"
}

case class Coprod_UnivProp_split(A: Obj, B: Obj, Z: Obj) extends HomMapping {
  def dom = Hom(A U B, Z)
  def cod = Hom(A, Z) x Hom(B, Z)
  protected def _apply(arg: List[Mor]): List[Mor] = { 
    val fg = arg.head
    List(fg o I1(A, B), fg o I2(A, B))
  }
  def substitute(s: Map[String, Obj]) = Coprod_UnivProp_split(
    substObj(s, A),
    substObj(s, B),
    substObj(s, Z)
  )
  def inverse = Some(Coprod_UnivProp_mediating(A, B, Z))
  def toTex = {
    "(- \\circ \\iota_1^{ %1$s,%2$s}, - \\circ \\iota_2^{ %1$s,%2$s})".
    format(A.toTex, B.toTex)
  }
}

case class Exp_UnivProp_curry(A: Obj, B: Obj, Z: Obj) extends HomMapping {
  def dom = Hom(A x B, Z)
  def cod = Hom(A, Exp(Z, B))
  protected def _apply(arg: List[Mor]): List[Mor] = List(Lambda(arg.head))
  def substitute(s: Map[String, Obj]) = Exp_UnivProp_curry(
    substObj(s, A),
    substObj(s, B),
    substObj(s, Z)
  )
  def inverse = Some(Exp_UnivProp_uncurry(A, B, Z))
  def toTex = "\\lambda"
}

case class Exp_UnivProp_uncurry(A: Obj, B: Obj, Z: Obj) extends HomMapping {
  def dom = Hom(A, Exp(Z, B))
  def cod = Hom(A x B, Z)
  protected def _apply(arg: List[Mor]) = 
    List(Eval(B, Z) o times(arg.head, Id(B)))
  def substitute(s: Map[String, Obj]) = Exp_UnivProp_uncurry(
    substObj(s, A),
    substObj(s, B),
    substObj(s, Z)
  )
  def inverse = Some(Exp_UnivProp_curry(A, B, Z))
  def toTex = {
    "\\textrm{eval}^{ %1$s,%2$s} \\circ (- \\times \\textrm{Id}_{ %1$s})".
    format(B.toTex, Z.toTex)
  }
}

case class MorphismCompositionHomMapping(A: Obj, B: Obj, C: Obj) 
extends HomMapping {
  def dom = Hom(A, B) x Hom(B, C)
  def cod = Hom(A, C)
  protected def _apply(args: List[Mor]) = 
    List(args(0) o args(1))
  def substitute(s: Map[String, Obj]) = MorphismCompositionHomMapping(
    substObj(s, A),
    substObj(s, B),
    substObj(s, C)
  )
  def inverse = None
  def toTex = "- \\circ -"
}

val DefaultPatterns = {
  val A = AtomObj("A")
  val B = AtomObj("B")
  val Z = AtomObj("Z")
  List(
    Prod_UnivProp_mediating(Z, A, B),
    Prod_UnivProp_split(Z, A, B),
    Coprod_UnivProp_mediating(A, B, Z),
    Coprod_UnivProp_split(A, B, Z),
    Exp_UnivProp_curry(A, B, Z),
    Exp_UnivProp_uncurry(A, B, Z),
    MorphismCompositionHomMapping(A, B, Z)
  )
}

/*##############################################################################
                  Pattern-matching on objects and  hom-sets
##############################################################################*/
type Match = Map[String, Obj]
/**
  * Merges two matches into a single one, if possible. Fails if both matches
  * contain incompatible information.
  */
def mergeMatches(x: Match, y: Match): Option[Match] = { 
  val keys = x.keySet ++ y.keySet
  var res = new scala.collection.mutable.HashMap[String, Obj]
  for (k <- keys) {
    if (x.contains(k)) {
      if (y.contains(k)) {
        val xv = x(k)
        val yv = y(k)
        if (xv == yv) {
          res(k) = xv
        } else {
          // two incompatible values, that's bad
          return None
        }
      } else {
        res(k) = x(k)
      }
    } else if (y.contains(k)) {
      res(k) = y(k)
    } else {
      throw new Error("Either `Map.keySet` or the merging algo has a bug")
    }
  }
  return Some(res.toMap)
}

/**
  * Tries to combine all `matches` into a single `Match`. Fails
  * if the `Match` instances in input are incompatible.
  */
def mergeMatches(matches: List[Match]): Option[Match] = {
  matches match {
    case Nil => Some(Map.empty)
    case h :: t => 
      for (tm <- mergeMatches(t); res <- mergeMatches(h, tm)) yield res
  }
}

/**
  * Tries to generate an assignment of atomic object names from `pat` to
  * sub-objects from which `inst` is built.
  */
def objPatternMatching(inst: Obj, pat: Obj): Option[Match] = {
  (inst, pat) match {
    case (Prod(a, b), Prod(p, q)) => objPatternMatching_2(a, b, p, q)
    case (Coprod(a, b), Coprod(p, q)) => objPatternMatching_2(a, b, p, q)
    case (Exp(a, b), Exp(p, q)) => objPatternMatching_2(a, b, p, q)
    case (x, AtomObj(name)) => Some(Map(name -> x))
    case (Terminal, Terminal) => Some(Map.empty)
    case (Initial, Initial) => Some(Map.empty)
    case _ => None
  }
}

/**
  * Tries to match `a` against `p` and `b` against `q`, succeeds only if
  * both matches are compatible
  */
def objPatternMatching_2(a: Obj, b: Obj, p: Obj, q: Obj): Option[Match] = { 
  for {
    ma <- objPatternMatching(a, p)
    mb <- objPatternMatching(b, q)
    mrg <- mergeMatches(ma, mb)
  } yield mrg
}

/**
  * Attempts to match thingies like `Hom[A_1, B_1] x ... x Hom[A_n, B_n]`
  * against each other. Returns some map with suitable substitutions for 
  * every atomic object that occurs in `pat` in case of success, or `None`
  * otherwise.
  */
def homPatternMatching(inst: HomProd, pat: HomProd): Option[Match] = {
  val HomProd(insts) = inst
  val HomProd(pats) = pat
  if (insts.size == pats.size) {
    val componentMatches = 
      for ((Hom(a, b), Hom(p, q)) <- insts zip pats) 
      yield objPatternMatching_2(a, b, p, q)
    // if every component matched, and all their matches were 
    // compatible, then we have a match
    for (
      ms <- sequence(componentMatches);
      mrg <- mergeMatches(ms)
    ) yield mrg
  } else {
    // not even the number of components is the same, no match
    None
  }
}

/*##############################################################################
      Treating objects as variables in more complex objects and morphisms
##############################################################################*/
def substObj(s: Map[String, Obj], obj: Obj): Obj = obj match {
  case AtomObj(name) => {
    if (s.isDefinedAt(name)) s(name)
    else AtomObj(name)
  }
  case Terminal => Terminal
  case Initial => Initial
  case Prod(a, b) => Prod(substObj(s,a), substObj(s, b))
  case Coprod(a, b) => Coprod(substObj(s, a), substObj(s, b))
  case Exp(a, b) => Exp(substObj(s, a), substObj(s, b))
}

def substMor(s: Map[String, Obj], mor: Mor): Mor = mor match {
  case Comp(g, f) => Comp(substMor(s, g), substMor(s, f))
  case Id(o) => Id(substObj(s, o))
  case P1(x, y) => P1(substObj(s, x), substObj(s, y))  
  case P2(x, y) => P2(substObj(s, x), substObj(s, y))  
  case I1(x, y) => I1(substObj(s, x), substObj(s, y))
  case I2(x, y) => I2(substObj(s, x), substObj(s, y))
  case ProdMor(g, f) => ProdMor(substMor(s, g), substMor(s, f))
  case CoprodMor(g, f) => CoprodMor(substMor(s, g), substMor(s, f))
  case Lambda(f) => Lambda(substMor(s, f))
  case Eval(a, b) => Eval(substObj(s, a), substObj(s, b))
  case InitMor(o) => InitMor(substObj(s, o))
  case TermMor(o) => TermMor(substObj(s, o))
  case VariableMor(name, a, b) => 
    VariableMor(name, substObj(s, a), substObj(s, b))
}

/*##############################################################################
                              Morphism searchers
##############################################################################*/
// the idea is this: 
// ultimately, we want to find `HomMapping`s automatically.
// - Finding permutations and cross-products-of-hom-mappings are essentially
// combinatoric problems. 
// - Finding out whether some universal property is applicable is simple
//   Obj-pattern matching
// - Finding the right morphisms for the `HomBifunctor`
//   is more difficult (notice that it is the only type of hom-mapping that
//   is parameterized by morphisms, not merely objects)
// The raison d'etre of morphism searchers is to find suitable morphisms that
// can be plugged into the `HomBifunctor`.

/**
  * An inference rule that tells us what subgoals have to be solved in order
  * to solve the final goal, and how to actually compose the final solution out
  * of solution of subgoals.
  */
trait MorphismConstructionRule {
  /**
    * Returns a list of subgoals, if this rule matches the goal.
    */
  def subgoals(dom: Obj, cod: Obj): Option[List[(Obj, Obj)]]

  /**
    * Constructs solution of the goal using solutions of subgoals,
    * a solution consists of a morphism from `dom` to `cod`, and an
    * optional inverse.
    */
  def apply(
    dom: Obj, 
    cod: Obj, 
    subgoalSolutions: List[(Mor, Option[Mor])]
  ): (Mor, Option[Mor])
}

/**
  * Checks whether variables in `f` can be replaced in such a way that
  * they match `cod` and `dom`. The most basic kind of rule, produces no
  * subgoals.
  */
case class PatternMorConstrRule(
  pattern: Mor,
  inverse: Option[Mor]
) extends MorphismConstructionRule {
  // NOTE: this is why the interface 
  // `apply(dom, cod): Option[(List[(Obj, Obj)], List[Mor] => Mor)]`
  // actually made sense... We could optimize the double pattern matching
  // away there. But this is a minor optimization.

  /**
    * Returns `Some(Nil)` if the pattern matches, `None` otherwise.
    * Degenerated case, produces no subgoals.
    */
  def subgoals(dom: Obj, cod: Obj): Option[List[(Obj, Obj)]] = {
    for (_ <- objPatternMatching_2(dom, cod, pattern.dom, pattern.cod)) yield {
      Nil
    }
  }

  def apply(dom: Obj, cod: Obj, subgoalSolutions: List[(Mor, Option[Mor])]) = {
    val s = objPatternMatching_2(dom, cod, pattern.dom, pattern.cod).get
    (substMor(s, pattern), for {i <- inverse} yield substMor(s, i))
  }
}

/**
  * A rule that builds `(f x g)` from `f` and `g`
  */
case object ProdMorConstrRule extends MorphismConstructionRule {
  def subgoals(dom: Obj, cod: Obj): Option[List[(Obj, Obj)]] = {
    (dom, cod) match {
      case (Prod(a, b), Prod(c, d)) => Some(List((a, c), (b, d)))
      case _ => None
    }
  }
  def apply(dom: Obj, cod: Obj, subgoalSolutions: List[(Mor, Option[Mor])]) = {
    val f = times(subgoalSolutions(0)._1, subgoalSolutions(1)._1)
    val fi =
      for (ai <- subgoalSolutions(0)._2; bi <- subgoalSolutions(1)._2) 
      yield times(ai, bi)
    (f, fi)
  }
}

/**
  * Builds `(f U g)` from `f` and `g`
  */
case object CoprodMorConstrRule extends MorphismConstructionRule {
  def subgoals(dom: Obj, cod: Obj): Option[List[(Obj, Obj)]] = {
    (dom, cod) match {
      case (Coprod(a, b), Coprod(c, d)) => Some(List((a, c), (b, d)))
      case _ => None
    }
  }
  def apply(dom: Obj, cod: Obj, subgoalSolutions: List[(Mor, Option[Mor])]) = {
    val f = amalg(subgoalSolutions(0)._1, subgoalSolutions(1)._1)
    val fi =
      for (ai <- subgoalSolutions(0)._2; bi <- subgoalSolutions(1)._2) 
      yield amalg(ai, bi)
    (f, fi)
  }
}

/**
  * Builds `B^A -> D^C` out of `C -> A` and `B -> D`
  */
case object LambdaMorConstrRule extends MorphismConstructionRule {
  def subgoals(dom: Obj, cod: Obj): Option[List[(Obj, Obj)]] = {
    (dom, cod) match {
      case (Exp(b, a), Exp(d, c)) => Some(List((c, a), (b, d)))
      case _ => None
    }
  }
  def apply(dom: Obj, cod: Obj, subgoalSolutions: List[(Mor, Option[Mor])]) = {
    val Exp(b, a) = dom
    val Exp(d, c) = cod
    val pre = subgoalSolutions(0)._1
    val post = subgoalSolutions(1)._1
    val f = Lambda(post o Eval(a, b) o times(Id(dom), pre))
    val pre_inv = subgoalSolutions(0)._2
    val post_inv = subgoalSolutions(1)._2
    val fi = 
      for (pri <- pre_inv; poi <- post_inv)
      yield Lambda(poi o Eval(c, d) o times(Id(cod), pri))
    (f, fi)
  }
}

val DefaultMorphismConstructionRules: List[MorphismConstructionRule] = {
  // declare some dummy-vars for patterns
  val A = AtomObj("A")
  val B = AtomObj("B")
  val C = AtomObj("C")
  val D = AtomObj("D")
  // id, commutativity
  val selfInverse = List(
    (Id(A), Id(A)),
    (ProdMor(P2(A, B), P1(A, B)), ProdMor(P2(B, A), P1(B, A))),
    (CoprodMor(I2(A, B), I1(A, B)), CoprodMor(I2(B, A), I1(B, A)))
  )

  // associativity, +0, *1
  val invertibleMorphisms = List(
    (ProdMor(
      P1(A, B) o P1(A x B, C), 
      ProdMor(P2(A, B) o P1(A x B, C), P2(A x B, C))
    ), // A x (B x C) ~ (A x B) x C
    ProdMor(
      ProdMor(P1(A, B x C), P1(B, C) o P2(A, B x C)),
      P2(B, C) o P2(A, B x C)
    )), // (A x B) x C ~ A x (B x C)
    
    (CoprodMor(
      CoprodMor(I2(A, B U C), I2(A, B U C) o I1(B, C)),
      I2(A, B U C) o I2(B, C)
    ),
    CoprodMor(
      I1(A U B, C) o I1(A, B),
      CoprodMor(I1(A U B, C) o I1(A, B) , I2(A U B, C))
    )),
    (P1(A, Terminal), ProdMor(Id(A), TermMor(A))),
    (P2(Terminal, A), ProdMor(TermMor(A), Id(A))),
    (I1(A, Initial), CoprodMor(Id(A), InitMor(A))),
    (I2(Initial, A), CoprodMor(InitMor(A), Id(A)))
  )

  val oneWayMorphisms = List(
    P1(A, B), P2(A, B), I1(A, B), I2(A, B), Eval(A, B),
    InitMor(A), TermMor(A)
  )

  // glue three subgoal-generating rules to 0-subgoal pattern rules
  val res = (
    for ((f, fi) <- selfInverse) 
    yield PatternMorConstrRule(f, Some(fi))
  ) ++ (
    for (
      (f, fi) <- invertibleMorphisms; 
      p <- List(
        PatternMorConstrRule(f, Some(fi)), 
        PatternMorConstrRule(fi, Some(f))
      )
    ) yield p
  ) ++(
    for (f <- oneWayMorphisms) 
    yield PatternMorConstrRule(f, None)
  ) ++ (
    List(
      ProdMorConstrRule,
      CoprodMorConstrRule,
      LambdaMorConstrRule
    )
  )

  // res foreach { 
  //   case PatternMorConstrRule(f, _) => println(f.toTex)
  //   case _ => {}
  // }

  res
}

/**
  * Attempts to find a canonical morphism from `dom` to `cod`
  * (and its inverse, if possible), using `allRules`.
  */
def searchMorphism(
  dom: Obj, 
  cod: Obj, 
  allRules: List[MorphismConstructionRule],
  mustBeInvertible: Boolean 
): Option[(Mor, Option[Mor])] = {
  def helper(activeRules: List[MorphismConstructionRule]): 
  Option[(Mor, Option[Mor])] = {
    activeRules match {
      case Nil => None
      case h :: t => (for (
        subgoals <- h.subgoals(dom, cod);
        solutions <- sequence(subgoals.map{ 
          g => searchMorphism(g._1, g._2, allRules, mustBeInvertible) 
        })
      ) yield h(dom, cod, solutions)) match {
        case solution @ Some((f, Some(fi))) => solution
        case nonInvrt @ Some((f, None)) => 
          if (mustBeInvertible) helper(t)
          else nonInvrt
        case None => helper(t)
      }
    }
  }
  helper(allRules)
}

/*##############################################################################
                             Hom-mapping searchers
##############################################################################*/

/**
  * Some generic strategy that attempts to reconstruct a 
  * canonical morphism between sets with the structure
  * `Hom[A_1, B_1] x ... x Hom[A_n, B_n]`.
  */
trait HomMappingSearcher {
  def tryFindMapping(
    dom: HomProd, 
    cod: HomProd, 
    mustBeInvertible: Boolean
  ): Option[HomMapping]
}

/**
  * Finds a bijection between 
  * `Hom[A_1, B_1] x ... x Hom[A_n, B_n]` and 
  * `Hom[C_1, D_1] x ... x Hom[C_n, D_n]` iff
  * the two sets differ by a permutation of factors.
  */
case object PermutationSearcher extends HomMappingSearcher {
  def tryFindMapping(
    dom: HomProd, 
    cod: HomProd, 
    mustBeInvertible: Boolean
  ): Option[HomMapping] = {
    for (pi <- extractPermutation(dom.factors, cod.factors)) yield {
      PermutationHomMapping(pi, dom.factors.toVector)
    }
  }
}

/**
  * Attempts to subdivide the products
  * `Hom[A_1, B_1] x ... x Hom[A_n, B_n]` and 
  * `Hom[C_1, D_1] x ... x Hom[C_m, D_m]`, and 
  * find a simpler mapping for each pair of
  * corresponding partitions. All partitions are
  * contiguous, permuting the factors is not attempted.
  */
case class CrossProdOfHomMappingsSearcher(
  childSearchers: List[HomMappingSearcher] 
) extends HomMappingSearcher {
  def tryFindMapping(
    dom: HomProd, 
    cod: HomProd, 
    mustBeInvertible: Boolean
  ): Option[HomMapping] = {
    val maxK = Math.min(dom.factors.size, cod.factors.size)
    for (
      k <- (1 to maxK).reverse;
      domsFactors <- linearPartitions(k, dom.factors);
      codsFactors <- linearPartitions(k, cod.factors)
    ) {
      val doms = domsFactors.map{ fs => HomProd(fs) }
      val cods = codsFactors.map{ fs => HomProd(fs) }
      val subGoals = doms zip cods
      val subgoalSolutions = 
        findAll(subGoals) {  g => 
          val (sg_dom, sg_cod) = g
          findSome(childSearchers) { c => 
            c.tryFindMapping(sg_dom, sg_cod, mustBeInvertible)
          }
        }
      subgoalSolutions match {
        case Some(mappings) => return Some(CrossProdOfHomMappings(mappings))
        case None => {/* do nothing, continue with next k */}
      }
    }
    None
  }
}

/**
  * Attempts to identify a mapping as a special instance 
  * of a pattern from a list of predefined basic patterns.
  */
case class PredefinedPatternSearcher(
  patterns: List[HomMapping]
) extends HomMappingSearcher {
  def tryFindMapping(
    dom: HomProd, 
    cod: HomProd, 
    mustBeInvertible: Boolean
  ): Option[HomMapping] = {
    for (p <- patterns) {
      if (!mustBeInvertible || p.isInvertible) {
        for (
          d <- homPatternMatching(dom, p.dom);
          c <- homPatternMatching(cod, p.cod);
          mrg <- mergeMatches(d, c)
        ) {
          return Some(p.substitute(mrg))
        }
      }
    }
    None
  }
}

/**
  * Attempts to find a `HomBifunctor` mapping between hom-sets
  * (that is, tries to find some canonical morphisms that can be 
  * pre-composed and post-composed).
  */
case class HomBifunctorMappingSearcher(
  morConstrRules: List[MorphismConstructionRule] = 
    DefaultMorphismConstructionRules
) extends HomMappingSearcher {
  def tryFindMapping(
    dom: HomProd,
    cod: HomProd,
    mustBeInvertible: Boolean
  ): Option[HomMapping] = {
    if (dom.factors.size != 1 || cod.factors.size != 1) None
    else {
      val Hom(a, b) = dom.factors.head
      val Hom(c, d) = cod.factors.head
      
      for (
        (pre,pre_inv) <- searchMorphism(c, a, morConstrRules, mustBeInvertible);
        (pst,pst_inv) <- searchMorphism(b, d, morConstrRules, mustBeInvertible)
      ) yield {
        HomBifunctor(pre, pre_inv, pst, pst_inv)
      }
    }
  }
}

val DefaultSearchers = {
  List(
    PermutationSearcher,
    PredefinedPatternSearcher(DefaultPatterns),
    CrossProdOfHomMappingsSearcher(
      List(
        HomBifunctorMappingSearcher(),
        PredefinedPatternSearcher(DefaultPatterns) 
      )
    )
  )
}

/*##############################################################################
                        Sequences of hom-set definitions
##############################################################################*/

/**
  * Attempts to find a canonical `HomMapping` that maps between `dom` and `cod`.
  */
def findSingleStepMapping(
  dom: HomProd, 
  cod: HomProd, 
  mustBeInvertible: Boolean,
  searchers: List[HomMappingSearcher] = DefaultSearchers
): Option[HomMapping] = { 
  for (s <- searchers) {
    // println("DEBUG:  applying searcher " + s.toString.take(50))
    s.tryFindMapping(dom, cod, mustBeInvertible) match {
      case Some(solution) => return Some(solution)
      case None => {/* do nothing, try next} */}
    }
  }
  None
}

/**
  * A sequence of products of hom-sets that determines a morphism
  * "quasi-uniquely for many practical purposes" (given the right set
  * of patterns).
  */
case class HomSeq(
  steps: List[HomProd], 
  mustBeInvertible: List[Boolean]
) {
  def ~(homs: HomProd): HomSeq = HomSeq(
    steps :+ homs,
    mustBeInvertible :+ true
  )
  def ->(homs: HomProd): HomSeq = HomSeq(
    steps :+ homs,
    mustBeInvertible :+ false
  )
  def canonicalMapping(
    searchers: List[HomMappingSearcher] = DefaultSearchers
  ): Option[HomMappingComposition] = {
    val singleStepMappingOpts = 
      for (((a, b), ivt) <- steps.zip(steps.tail).zip(mustBeInvertible))
      yield findSingleStepMapping(a, b, ivt, searchers)
    val singleStepMappings = sequence(singleStepMappingOpts)
    singleStepMappings.map{ mappings => HomMappingComposition(mappings) }
  }
}

/*##############################################################################
                        Morphism "beautification"
##############################################################################*/

/**
  * Kind-of half-hearted pseudo-normalization, that at least eliminates the
  * composition with identity morphisms
  */

def beautify(m: Mor): Mor = m match {
  // eliminating identities
  case Comp(Id(_), f) => beautify(f)
  case Comp(f, Id(_)) => beautify(f)
  // gluing morphism cross-products into product morphisms
  case Comp(
    ProdMor(Comp(f, P1(_,_)), Comp(g, P2(_,_))), 
    ProdMor(z, w)
  ) => ProdMor(beautify(f o z), beautify(g o w))
  // gluing morphisms amalgs into coproduct morphisms
  case Comp(
    CoprodMor(z, w),
    CoprodMor(Comp(I1(_,_), f), Comp(I2(_,_), g))
  ) => CoprodMor(beautify(z o f), beautify(w o g))
  case Comp(f, g) => {
    val bf = beautify(f)
    val bg = beautify(g)
    if (bf != f || bg != g) beautify(bf o bg)
    else (bf o bg)
  }
  case ProdMor(f, g) => ProdMor(beautify(f), beautify(g))
  case CoprodMor(f, g) => CoprodMor(beautify(f), beautify(g))
  case Lambda(f) => Lambda(beautify(f))
  case sthElse => sthElse
}

/*##############################################################################
              Extraction of isomorphisms using Yoneda-lemma
##############################################################################*/
/**
  * Extracts isomorphism between `A` and `B` from 
  * natural isomorphism and `Hom[A, Y]` and `Hom[B, Y]`.
  */
def extractIso_left(naturalIso: HomMapping): (Mor, Mor) = {
  require(naturalIso.dom.factors.size == 1, "Expected 1 Hom-set in domain")
  require(naturalIso.cod.factors.size == 1, "Expected 1 Hom-set in codomain")
  val hom1 = naturalIso.dom.factors.head
  val hom2 = naturalIso.cod.factors.head
  val AtomObj(y) = hom1.cod
  val a = hom1.dom
  val b = hom2.dom
  val f = (naturalIso.inverse.get.substitute(Map(y -> b)))(List(Id(b))).head
  val fi = (naturalIso.substitute(Map(y -> a)))(List(Id(a))).head
  (beautify(f), beautify(fi))
}

/**
  * Extracts isomorphism between `A` and `B` from 
  * natural isomorphism and `Hom[Y, A]` and `Hom[Y, B]`.
  */
def extractIso_right(naturalIso: HomMapping): (Mor, Mor) = {
  require(naturalIso.dom.factors.size == 1, "Expected 1 Hom-set in domain")
  require(naturalIso.cod.factors.size == 1, "Expected 1 Hom-set in codomain")
  val hom1 = naturalIso.dom.factors.head
  val hom2 = naturalIso.cod.factors.head
  val AtomObj(y) = hom1.dom
  val a = hom1.cod
  val b = hom2.cod
  val f = (naturalIso.substitute(Map(y -> a)))(List(Id(a))).head
  val fi = (naturalIso.inverse.get.substitute(Map(y -> b)))(List(Id(b))).head
  (beautify(f), beautify(fi))
}

/*##############################################################################
       github specific DSL for generating bunch of images in README
##############################################################################*/

def saveDiagram(name: String, tex: String): Unit = {
  import java.io._
  val file = new File(name + ".tex")
  if (file.exists()) { /* do nothing */ } 
  else {
    val writer = new BufferedWriter(new FileWriter(file))
    writer.write(tex)
    writer.close()
  }
}


def h3(title: String): Unit = { println("### " + title) }
def par(text: String): Unit = { println("\n\n" + text + "\n\n") }
def inlineCode(c: String): String = s"`$c`"
def code(src: String): Unit = { println("\n\n```scala\n" + src + "\n```\n\n") }
def texCode(src: String): Unit = { println("\n\n```latex\n" + src + "\n```\n\n") }

def generateIsoParagraph(iso: Mor, iso_inv: Mor): Unit = {
  par("Isomorphisms extracted using Yoneda lemma between objects %s and %s:".
    format(
      inlineCode(iso.dom.toCode),
      inlineCode(iso.cod.toCode)
    )
  )
  
  texCode(iso.toTex)
  texCode(iso_inv.toTex)
}

def figure(alt: String, file: String): Unit = println(s"\n\n![$alt]($file)")

def hline(): Unit = println("-----")

/*##############################################################################
                Generate readme with a header and a bunch of examples
##############################################################################*/

// Print out the fixed README header.
scala.io.Source.fromFile("readmeHeader.md").getLines.foreach(println)

// Bunch of variables to formulate the statements
val A = AtomObj("A")
val B = AtomObj("B")
val C = AtomObj("C")
val D = AtomObj("D")
val E = AtomObj("E")
val X = AtomObj("X")
val Y = AtomObj("Y")

/* Distributivity of products over coproducts, from right */ {
  val eqChain = (
    Hom((A U B) x C, Y) ~
    Hom(A U B, Y^C) ~
    (Hom(A, Y^C) x Hom(B, Y^C)) ~
    (Hom(A x C, Y) x Hom(B x C, Y)) ~
    Hom((A x C) U (B x C), Y)
  )
  val natIso = eqChain.canonicalMapping().get
  val (iso, iso_inv) = extractIso_left(natIso)

  // printing results
  saveDiagram("distrib_right", natIso.toDiagram(true))
  h3("Distributivity of product over coproduct (from right)")
  par("Scala code:")
  code(
  """
    |Hom((A U B) x C, Y) ~
    |Hom(A U B, Y^C) ~
    |(Hom(A, Y^C) x Hom(B, Y^C)) ~
    |(Hom(A x C, Y) x Hom(B x C, Y)) ~
    |Hom((A x C) U (B x C), Y)
  """.stripMargin
  )
  par(
    "Inferred canonical natural isomorphism between hom-sets:"
  )
  figure("distrib_right", "distrib_right.svg")
  generateIsoParagraph(iso, iso_inv)
}

hline()

/* Distributivity of products over coproducts */ {
  val eqChain = (
    Hom(C x (A U B), Y) ~
    Hom((A U B) x C, Y) ~
    Hom(A U B, Y^C) ~
    (Hom(A, Y^C) x Hom(B, Y^C)) ~
    (Hom(A x C, Y) x Hom(B x C, Y)) ~
    Hom((A x C) U (B x C), Y) ~
    Hom((C x A) U (C x B), Y)
  )
  val natIso = eqChain.canonicalMapping().get
  val (iso, iso_inv) = extractIso_left(natIso)

  // printing results
  saveDiagram("distrib_left", natIso.toDiagram(true))
  h3("Distributivity of product over coproduct (from left)")
  par("Scala code:")
  code(
  """
    Hom(C x (A U B), Y) ~
    Hom((A U B) x C, Y) ~
    Hom(A U B, Y^C) ~
    (Hom(A, Y^C) x Hom(B, Y^C)) ~
    (Hom(A x C, Y) x Hom(B x C, Y)) ~
    Hom((A x C) U (B x C), Y) ~
    Hom((C x A) U (C x B), Y)
  """
  )
  par("Constructed canonical natural isomorphism:")
  figure("distrib_left", "distrib_left.svg")
  generateIsoParagraph(iso, iso_inv)
}

hline()

/* Finding an isomorphism between C^(A x B) and (C^A)^B */ {
  val eqChain = (
    Hom(D, Exp(C, A x B)) ~
    Hom(D x (A x B), C) ~
    Hom(D x (B x A), C) ~
    Hom((D x B) x A, C) ~
    Hom(D x B, Exp(C, A)) ~
    Hom(D, Exp(Exp(C, A), B))
  )
  val natIso = eqChain.canonicalMapping().get
  val (iso, iso_inv) = extractIso_right(natIso)

  // printing results
  saveDiagram("powTimes", natIso.toDiagram(true))
  h3("Iterated exponentiation")
  par("Scala code:")
  code(
  """
    |Hom(D, Exp(C, A x B)) ~
    |Hom(D x (A x B), C) ~
    |Hom(D x (B x A), C) ~
    |Hom((D x B) x A, C) ~
    |Hom(D x B, Exp(C, A)) ~
    |Hom(D, Exp(Exp(C, A), B))
  """.stripMargin
  )
  par("Constructed canonical natural isomorphism:")
  figure("powTimes", "powTimes.svg")
  generateIsoParagraph(iso, iso_inv)
}

hline()

/* powPlus */ {
  val eqChain = (
    Hom(Y, (C^A) x (C^B)) ~
    (Hom(Y, C^A) x Hom(Y, C^B)) ~
    (Hom(Y x A, C) x Hom(Y x B, C)) ~
    (Hom(A x Y, C) x Hom(B x Y, C)) ~
    (Hom(A, C^Y) x Hom(B, C^Y)) ~
    Hom(A U B, C^Y) ~
    Hom((A U B) x Y, C) ~
    Hom(Y x (A U B), C) ~
    Hom(Y, C^(A U B))
  )
  val natIso = eqChain.canonicalMapping().get
  val (iso, iso_inv) = extractIso_right(natIso)

  // printing results
  val diagName = "powPlus"
  saveDiagram(diagName, natIso.toDiagram(true))
  h3("Product of exponents")
  par("Scala code:")
  code(
  """
    |Hom(Y, (C^A) x (C^B)) ~
    |(Hom(Y, C^A) x Hom(Y, C^B)) ~
    |(Hom(Y x A, C) x Hom(Y x B, C)) ~
    |(Hom(A x Y, C) x Hom(B x Y, C)) ~
    |(Hom(A, C^Y) x Hom(B, C^Y)) ~
    |Hom(A U B, C^Y) ~
    |Hom((A U B) x Y, C) ~
    |Hom(Y x (A U B), C) ~
    |Hom(Y, C^(A U B))
  """.stripMargin
  )
  par("Constructed canonical natural isomorphism:")
  figure(diagName, s"$diagName.svg")
  generateIsoParagraph(iso, iso_inv)
}

hline()

/* prodPow */ {
  val eqChain = (
    Hom(Y, (A x B)^C) ~
    Hom(Y x C, A x B) ~
    (Hom(Y x C, A) x Hom(Y x C, B)) ~
    (Hom(Y, A^C) x Hom(Y, B^C)) ~
    Hom(Y, (A^C) x (B^C))
  )
  val natIso = eqChain.canonicalMapping().get
  val (iso, iso_inv) = extractIso_right(natIso)

  // printing results
  val diagName = "prodPow"
  saveDiagram(diagName, natIso.toDiagram(true))
  h3("Exponent of products")
  par("Scala code:")
  code(
  """
    |Hom(Y, (A x B)^C) ~
    |Hom(Y x C, A x B) ~
    |(Hom(Y x C, A) x Hom(Y x C, B)) ~
    |(Hom(Y, A^C) x Hom(Y, B^C)) ~
    |Hom(Y, (A^C) x (B^C))
  """.stripMargin
  )
  par("Generated canonical natural isomorphism:")
  figure(diagName, s"$diagName.svg")
  generateIsoParagraph(iso, iso_inv)
}

hline()

/* powOne */ {
  val eqChain = (
    Hom(Y, A^Terminal) ~
    Hom(Y x Terminal, A) ~
    Hom(Y, A)
  )
  val natIso = eqChain.canonicalMapping().get
  val (iso, iso_inv) = extractIso_right(natIso)

  // printing results
  val diagName = "powOne"
  saveDiagram(diagName, natIso.toDiagram(true))
  h3("The rule \\(A^1 = A\\)")
  par("Scala code:")
  code(
  """
    |Hom(Y, A^Terminal) ~
    |Hom(Y x Terminal, A) ~
    |Hom(Y, A)
  """.stripMargin
  )
  par("Generated canonical natural isomorphism:")
  figure(diagName, s"$diagName.svg")
  generateIsoParagraph(iso, iso_inv)
}

hline()

/* powZero */ {
  val eqChain = (
    Hom(Terminal, A^Initial) ~
    Hom(Terminal x Initial, A) ~
    Hom(Initial, A)
  )
  val natIso = eqChain.canonicalMapping().get
  val natIso_inv = natIso.inverse.get
  val f = beautify(natIso_inv(List(InitMor(A))).head)

  // printing results
  val diagName = "powZero"
  saveDiagram(diagName, natIso.toDiagram(true))
  h3("The rule \\(A^0 = 1\\)")
  par("Scala code:")
  code(
  """
    |Hom(Terminal, A^Initial) ~
    |Hom(Terminal x Initial, A) ~
    |Hom(Initial, A)
  """.stripMargin
  )
  
  figure(diagName, s"$diagName.svg")
  par(
    "Here, we cannot (and need not) use the Yoneda-lemma. " + 
    "Instead, we simply apply the inverse of the above natural isomorphism " +
    "to the morphism `!_A`, and obtain a morphism from the terminal " +
    "object to `A^{\\mathbb{I}}`. Hence we obtain that " +
    "`A^{\\mathbb{I}}` must be isomorphic to the terminal object."
  )
  code(
    InitMor(A).toCode + "\n\n" + f.toCode
  )
}

hline()

/* disjElim */ {
  val eqChain = (
    (Hom(D, C^A) x Hom(D, C^B) x Hom(D, A U B)) ~
    (Hom(D x A, C) x Hom(D x B, C) x Hom(D, A U B)) ~
    (Hom(A x D, C) x Hom(B x D, C) x Hom(D, A U B)) ~
    (Hom(A, C^D) x Hom(B, C^D) x Hom(D, A U B)) ~
    (Hom(A U B, C^D) x Hom(D, A U B)) ~
    (Hom((A U B) x D, C) x Hom(D, A U B)) ~
    (Hom(D x (A U B), C) x Hom(D, A U B)) ~
    (Hom(D, C^(A U B)) x Hom(D, A U B)) ~
    Hom(D, (C^(A U B)) x (A U B)) ->
    Hom(D, C)
  )
  val natTrafo = eqChain.canonicalMapping().get
  
  // print the results
  val diagName = "disjElim"
  saveDiagram(diagName, natTrafo.toDiagram(false))
  h3("Analogon of the disjunction elimination")
  par("Scala code:")
  code(
  """
    |(Hom(D, C^A) x Hom(D, C^B) x Hom(D, A U B)) ~
    |(Hom(D x A, C) x Hom(D x B, C) x Hom(D, A U B)) ~
    |(Hom(A x D, C) x Hom(B x D, C) x Hom(D, A U B)) ~
    |(Hom(A, C^D) x Hom(B, C^D) x Hom(D, A U B)) ~
    |(Hom(A U B, C^D) x Hom(D, A U B)) ~
    |(Hom((A U B) x D, C) x Hom(D, A U B)) ~
    |(Hom(D x (A U B), C) x Hom(D, A U B)) ~
    |(Hom(D, C^(A U B)) x Hom(D, A U B)) ~
    |Hom(D, (C^(A U B)) x (A U B)) ->
    |Hom(D, C)
  """.stripMargin
  )
  par("Generated morphism:")
  figure(diagName, s"$diagName.svg")
  /*
  par("Here is what we obtain if we throw three parameters " + 
    "\\( (a, b, f) \\) into this mapping: " +
    "\\[\n" +
    beautify(natTrafo(List(
      VariableMor("a", D, Exp(C, A)),
      VariableMor("b", D, Exp(C, B)),
      VariableMor("f", D, A U B)
    )).head).toTex +
    "\\]\n</p>\n"
  )
  */
}

/*
// Example: walking along the edges of associahedron
val expl_assoc = (
  Hom( ((A x ((B x C) x D)) x E), X) ~
  Hom( (A x (((B x C) x D) x E)), X) ~
  Hom( (A x ((B x C) x (D x E))), X) ~
  Hom( (A x (B x (C x (D x E)))), X)
).canonicalMapping().get
println(expl_assoc)
println(expl_assoc.inverse)
val g = VariableMor("g", 
  ((A x ((B x C) x D)) x E),
  X
)
println(beautify(expl_assoc(List(g)).head))

// Example: permutation check
val expl_permut = (
  (Hom(A, B) x Hom(C, D) x Hom(C, A)) ~
  (Hom(C, D) x Hom(C, A) x Hom(A, B)) ~
  (Hom(C, A) x Hom(A, B) x Hom(C, D))
).canonicalMapping().get
println(expl_permut)
println(expl_permut.inverse)

*/
