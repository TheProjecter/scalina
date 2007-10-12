package scalina

import scala.examples.tcpoly.binding.frescala._

/*
  l, L, x metavars (value labels, type labels, variables)
  t = t "." l   
    | t "<{" cm "}"   
    | "new" T       
  p = ... // subset of terms -- until we add effects, could include all terms
  v = "new" T
  
  T = T "#" L 
    | T "<{" cm "}" // 
    | T "&" T  
    | "{" bind(x) (":" T)? "=>" in(m*) "}" = R
    | p "." type 
    | "Un[" T "]" // the type of a deferred value member, TODO: or of any type that contains members with this type
    
  m = "val" l ":" T
    | "val" l ":" T "=" t
    | "type" L ":" K
    | "type" L ":" K "=" T    

  K =  "Un[" K "]" 
    | "In(" T "," T ")"  
    | "*(" R ")"
    | "Struct(" R ")"    
    | "Nom(" R ")"
      
  cm = "val" l "=" t | "type" L "=" T  

*/
trait Syntax { self: ScalinaAbsM with Binding with Substitution with BindingSyntax with Syntax =>
  sealed abstract class Label
      case class V(name: Symbol) extends Label
      case class T(name: Symbol) extends Label
      
  // substitution may replace:
  //  - Var by Term
  //  - Single(Var) by Type
  trait Element
  
  trait Entity[T <: Entity[T]] extends Nominal[T] with Element with CheckingEquality[T]

  sealed abstract class Term extends Entity[Term] {
    def isPath: Boolean
    def isValue: Boolean
    
    def ===(o: Term) = (this, o) match {
      case ( _ , x: MetaTerm) => x === this // delegate to MetaTerm
      case (Var(n) , Var(n2) ) => n == n2
      case (SelV(tgt, l) , SelV(tgt2, l2) ) => tgt === tgt2 && l == l2
      case (RfnV(tgt, cm) , RfnV(tgt2, cm2) ) => tgt === tgt2 && cm === cm2
      case (New(tp) , New(tp2) ) => tp === tp2
      case _ => false
    }
  }

  case class Var(n: Name) extends Term {
    def isPath = true
    def isValue = false

    def swap(a: Name, b: Name) = Var(n swap(a, b))
    def fresh(a: Name) = n.fresh(a)
    def supp = n.supp
  }  
  
  case class SelV(tgt: Term, l: V) extends Term {
    def isPath = tgt.isPath
    def isValue = false    
    
    def swap(a: Name, b: Name) = SelV(tgt swap(a, b), l)
    def fresh(a: Name) = tgt.fresh(a)
    def supp = tgt.supp
  }
  
  case class RfnV(tgt: Term, cm: RefineMember) extends Term {
    def isPath = false
    def isValue = false  
    
    def swap(a: Name, b: Name) = RfnV(tgt swap(a, b), cm swap(a, b))
    def fresh(a: Name) = tgt.fresh(a) && cm.fresh(a)
    def supp = tgt.supp ::: cm.supp
  }
  
  case class New(tp: Type) extends Term {
    def isPath = true
    def isValue = true          
    
    def swap(a: Name, b: Name) = New(tp swap(a, b))
    def fresh(a: Name) = tp.fresh(a)
    def supp = tp.supp
  }


  trait Classifier[Self, T <: Entity[T]] extends Nominal[Self] with Element with CheckingEquality[Self] {
    def isUn: Boolean = false // overridden in UnK / UnT
  }


  
  sealed abstract class Type extends Entity[Type] with Classifier[Type, Term] {
    def ===(o: Type) = {println(this+"==="+o);
    (this, o) match {
      case (Unrolled(a), Unrolled(b)) => a == b // use shallow equality (otherwise we keep unrolling selftypes ad infinitum)
      case ( _ , x: MetaTp) => x === this // delegate to MetaTp
      case (SelT(tgt, l) , SelT(tgt2, l2) ) => tgt === tgt2 && l == l2
      case (RfnT(tgt, cm) , RfnT(tgt2, cm2) ) => tgt === tgt2 && cm === cm2
      case (a@Tmpl(_, body), b@Tmpl(_, body2) ) => a.selfType === b.selfType && body === body2
      case (MixT(tp1, tp2) , MixT(tp12, tp22) ) => tp1 === tp12 && tp2 === tp22 
      case (Sngl(path) , Sngl(path2) ) => path === path2
      case (AnyT , AnyT ) => true      
      case (NothingT , NothingT ) => true
      case (UnT(un) , UnT(un2) ) => un === un2
      case (BoxT(tp) , BoxT(tp2) ) => tp === tp2
      case _ => false
    }    }
  }


  case class SelT(tgt: Type, l: T) extends Type {
    def swap(a: Name, b: Name) = SelT(tgt swap(a, b), l)
    def fresh(a: Name) = tgt.fresh(a)
    def supp = tgt.supp
  }

  case class RfnT(tgt: Type, cm: RefineMember) extends Type {
    def swap(a: Name, b: Name) = RfnT(tgt swap(a, b), cm swap(a, b))
    def fresh(a: Name) = tgt.fresh(a) && cm.fresh(a)
    def supp = tgt.supp ::: cm.supp
  }
      
  case class Tmpl(selfTp: Option[Type], body: \\[Mems]) extends Type {
    def swap(a: Name, b: Name) = Tmpl(selfTp swap(a, b), body swap(a, b))
    def fresh(a: Name) = selfTp.fresh(a) && body.fresh(a)
    def supp = selfTp.supp ::: body.supp
    
    def selfType: Type = selfTp.getOrElse(Unrolled(this))
  }
      
  case class MixT(tp1: Type, tp2: Type) extends Type {
    def swap(a: Name, b: Name) = MixT(tp1 swap(a, b), tp2 swap(a, b))
    def fresh(a: Name) = tp1.fresh(a) && tp2.fresh(a)
    def supp = tp1.supp ::: tp2.supp
  }
      
  case class Sngl(path: Term) extends Type {
    def swap(a: Name, b: Name) = Sngl(path swap(a, b))
    def fresh(a: Name) = path.fresh(a)
    def supp = path.supp
  }
      
  case object AnyT extends Type {
    def swap(a: Name, b: Name) = this
    def fresh(a: Name) = true
    def supp = List()
  }
  
  case object NothingT extends Type  {
    def swap(a: Name, b: Name) = this
    def fresh(a: Name) = true
    def supp = List()
    
  }
  
  case class UnT(un: Type) extends Type { 
    override def isUn = true 
   
    def swap(a: Name, b: Name) = UnT(un swap(a, b))
    def fresh(a: Name) = un.fresh(a)
    def supp = un.supp
    
  }
  
  case class BoxT(tp: Type) extends Type { 
    def swap(a: Name, b: Name) = UnT(tp swap(a, b))
    def fresh(a: Name) = tp.fresh(a)
    def supp = tp.supp
    
  }  
  
 

  trait Member extends Nominal[Member] with Element with CheckingEquality[Member] {
    def deferred: Boolean
    val l: Label
    def nonAbstract: Boolean
    // a Set of members should not contain two members with the same label 
    override def equals(o: Any) = o match {
      case m: Member => m.l == l
      case _ => false
    }
    
    def ===(o: Member) = (this, o) match {
      case (MemV(l, c, r), MemV(l2, c2, r2)) => l == l2 && c === c2 && r === r2
      case (MemT(l, c, r), MemT(l2, c2, r2)) => l == l2 && c === c2 && r === r2
      case _ => false
    }
  }

  type Mems = Set[Member]
  
  implicit def addLookup(self: Mems): {def lookup(l: Label): AM[Member]} = new  {
    def lookup(l: Label): AM[Member] = self.find{_.l == l} map (AM.result(_)) getOrElse(AM.fail("no such member: "+l))
  }
  
  case class MemV(override val l : V, classifier: Type, res: Option[Term]) extends Member {
    def deferred: Boolean = classifier.isUn
    def nonAbstract = !res.isEmpty
    def swap(a: Name, b: Name) = MemV(l, classifier swap(a, b), res swap(a, b))
    def fresh(a: Name) = classifier.fresh(a) && res.fresh(a)
    def supp = classifier.supp ::: res.supp
  }

  case class MemT(override val l : T, classifier: Kind, res: Option[Type]) extends Member {
    def deferred: Boolean = classifier.isUn
    def nonAbstract = !res.isEmpty
    
    def swap(a: Name, b: Name) = MemT(l, classifier swap(a, b), res swap(a, b))
    def fresh(a: Name) = classifier.fresh(a) && res.fresh(a)
    def supp = classifier.supp ::: res.supp
  }


    
  trait RefineMember extends Nominal[RefineMember] with Element with CheckingEquality[RefineMember] {
    def ===(o: RefineMember) = (this, o) match {
      case (RMemV(l, r), RMemV(l2, r2)) => l == l2 && r === r2
      case (RMemT(l, r), RMemT(l2, r2)) => l == l2 && r === r2
      case _ => false
    }

  }
  
  case class RMemV(l : V, res: Term) extends RefineMember {  
    def swap(a: Name, b: Name) = RMemV(l, res swap(a, b))
    def fresh(a: Name) = res.fresh(a)
    def supp = res.supp
  }

  case class RMemT(l : T, res: Type) extends RefineMember {  
    def swap(a: Name, b: Name) = RMemT(l, res swap(a, b))
    def fresh(a: Name) = res.fresh(a)
    def supp = res.supp
  }


  sealed abstract class Kind extends Classifier[Kind, Type] {
    def ===(o: Kind): Boolean = (this, o) match {
      case ( _ , x: MetaKind) => x === this // delegate to MetaKind
      case (In(lower, upper) , In(lower2, upper2) ) => lower === lower2 && upper === upper2
      case (Struct(struct)   , Struct(struct2)   ) => struct === struct2
      case (NominalK(struct) , NominalK(struct2) ) => struct === struct2
      case (Concrete(struct) , Concrete(struct2) ) => struct === struct2
      case (UnK(un)          , UnK(un2)          ) => un === un2
      case _ => false
    }    
  }

  case class In(lower: Type, upper: Type) extends Kind {
    def swap(a: Name, b: Name) = In(lower swap(a, b), upper swap(a, b))
    def fresh(a: Name) = lower.fresh(a) && upper.fresh(a)
    def supp = lower.supp ::: upper.supp   
  }
  
  // really, struct: Tmpl, but that messes with Substable}
  case class Struct(struct: Type) extends Kind  {
    def swap(a: Name, b: Name) = Struct(struct swap(a, b))
    def fresh(a: Name) = struct.fresh(a)
    def supp = struct.supp
  }
  
  // really, struct: Tmpl, but that messes with Substable
  case class NominalK(struct: Type) extends Kind {
    def swap(a: Name, b: Name) = NominalK(struct swap(a, b))
    def fresh(a: Name) = struct.fresh(a)
    def supp = struct.supp
  }
   
  // really, struct: Tmpl, but that messes with Substable
  case class Concrete(struct: Type) extends Kind {
    def swap(a: Name, b: Name) = Concrete(struct swap(a, b))
    def fresh(a: Name) = struct.fresh(a)
    def supp = struct.supp
  }
 
  case class UnK(un: Kind) extends Kind { 
    override def isUn = true 
    
    def swap(a: Name, b: Name) = UnK(un swap(a, b))
    def fresh(a: Name) = un.fresh(a)
    def supp = un.supp
 }
 
       
    
  implicit def TermSubstTerm(self: Term): Substable[Term, Term] = new Substable[Term, Term] { 
    def subst(sub: Name => Option[Term]): AM[Term] = self match {
      case Var(n) => sub(n).getOrElse[Term](self)
      case SelV(tgt, l) => for(tgt2 <- tgt subst(sub)) yield SelV(tgt2, l)
      case RfnV(tgt, cm) => for(tgt2 <- tgt subst(sub); cm2 <- cm subst(sub)) yield RfnV(tgt2, cm2)
      case New(tp) => for(tp2 <- tp subst(sub)) yield New(tp2)
    }
  }
  
  def setTm[T <% Substable[Term, T]](o: Set[T]): Substable[Term, Set[T]] = new SubstTo[Term].SetIsSubstable(o)
  def optTm[T <% Substable[Term, T]](o: Option[T]): Substable[Term, Option[T]] = new SubstTo[Term].OptionIsSubstable(o)
  def absTm[T <% Substable[Term, T]](abs: \\[T]): Substable[Term, \\[T]] = new AbsSubstTo[Term].AbsIsSubstable(abs)
  
  implicit def TypeSubstTerm(self: Type): Substable[Term, Type] = new Substable[Term, Type] { 
    def subst(sub: Name => Option[Term]): AM[Type] = self match {
      case SelT(tgt, l) => for(tgt2 <- tgt subst(sub)) yield SelT(tgt2, l)
      case RfnT(tgt, cm) => for(tgt2 <- tgt subst(sub); cm2 <- cm subst(sub)) yield RfnT(tgt2, cm2) 
      case Tmpl(selfTp, body) => for(selfTp2 <- optTm(selfTp).subst(sub); 
                                    body2 <- absTm(body)(new SubstTo[Term].SetIsSubstable) subst(sub)) 
                                   yield Tmpl(selfTp2, body2)
      case MixT(tp1, tp2) => for(tp1a <- tp1 subst(sub); tp2a <- tp2 subst(sub)) yield MixT(tp1a, tp2a)
      case Sngl(path) => for(path2 <- path subst(sub)) yield Sngl(path2)
      case AnyT => AnyT
      case NothingT => NothingT
      case UnT(un) => for(un2 <- un subst(sub)) yield UnT(un2)
    }
  }
  
  implicit def MemberSubstTerm(self: Member): Substable[Term, Member] = new Substable[Term, Member] { 
    def subst(sub: Name => Option[Term]): AM[Member] = self match {
      case MemV(l, classifier, res) => for(classifier2 <- classifier subst(sub); res2 <- optTm(res) subst(sub)) yield MemV(l, classifier2, res2)
      case MemT(l, classifier, res) => for(classifier2 <- classifier subst(sub); res2 <- optTm(res) subst(sub)) yield MemT(l, classifier2, res2)
    }
  }
  
  implicit def RMemSubstTerm(self: RefineMember): Substable[Term, RefineMember] = new Substable[Term, RefineMember] { 
    def subst(sub: Name => Option[Term]): AM[RefineMember] = self match {
      case RMemV(l, res) => for(res2 <- res subst(sub)) yield RMemV(l, res2)
      case RMemT(l, res) => for(res2 <- res subst(sub)) yield RMemT(l, res2)
    }
  }
  
  implicit def KindSubstTerm(self: Kind): Substable[Term, Kind] = new Substable[Term, Kind] { 
    def subst(sub: Name => Option[Term]): AM[Kind] = self match {
      case In(lower, upper) => for(lower2 <- lower subst(sub); upper2 <- upper subst(sub)) yield In(lower2, upper2)
      case Struct(struct)   => for(struct2 <- struct subst(sub)) yield Struct(struct2)
      case NominalK(struct) => for(struct2 <- struct subst(sub)) yield NominalK(struct2)
      case Concrete(struct) => for(struct2 <- struct subst(sub)) yield Concrete(struct2)
      case UnK(un)          => for(un2 <- un subst(sub)) yield UnK(un2)        
    }       
  }
  
  
        
  // TODO: clean this up (should not appear outside of === in Type)
  // used when expanding implicit self types
  case class Unrolled(tp: Type) extends Type {
    def swap(a: Name, b: Name) = tp.swap(a,b)
    def fresh(a: Name) = tp.fresh(a)
    def supp = tp.supp
  }
  
  
  // term variable used by the type checker
  case class MetaTerm(override val isValue: Boolean, override val isPath: Boolean, override val tag: Tag, override val name: String, override var v: Option[Term]) extends Term with MetaVar[Term] {
    def unifies(o: Term) = Some(o)
  }  
  
  // type variable used by the type checker
  case class MetaTp(override val tag: Tag, override val name: String, override var v: Option[Type]) extends Type with MetaVar[Type] {
    def unifies(o: Type) = Some(o)
  }
    
  // TODO: buig hack!
  implicit def SetCEq[T <% CheckingEquality[T]](self: Set[T]): CheckingEquality[Set[T]] = new CheckingEquality[Set[T]] {
    def ===(other: Set[T]): Boolean = {
      self match { case meta: MetaMems => meta === other // delegate to MetaMems
                   case _ =>
      other match { 
        case meta: MetaMems => meta === other // delegate to MetaMems
        case _ => (true /: (for( s <- self; o <- other) yield s === o)) (_ && _)
      } 
      }
    }
  }
  
  case class MetaMems(requiredElems: Set[Member], override val tag: Tag, override val name: String, override var v: Option[Set[Member]]) extends scala.collection.immutable.HashSet[Member] with MetaVar[Set[Member]] {
    def unifies(o: Set[Member]) =  if(requiredElems forall {element => o exists {_ === element}}) Some(o) else None
  } 
  
    // kind variable used by the type checker
  case class MetaKind(override val tag: Tag, override val name: String, override var v: Option[Kind]) extends Kind with MetaVar[Kind] {
    def unifies(o: Kind) = Some(o)
  }
  
  def isVar     (x: Any): AM[(Name)] = x match { case Var(n) => println(x); AM.result((n))                                      case _ => AM.fail("expected Var") }
  def isSelV    (x: Any): AM[(Term, V)] = x match { case SelV(tgt, l) => println(x);AM.result((tgt, l)) case _ => AM.fail("expected SelV") }
  def isRfnV    (x: Any): AM[(Term, RefineMember)] = x match { case RfnV(tgt, cm) => AM.result((tgt, cm))                         case _ => AM.fail("expected RfnV") }
  def isNew     (x: Any): AM[(Type)] = x match { case New(tp) => AM.result((tp))                                    case _ => AM.fail("expected New") }
  def isSelT    (x: Any): AM[(Type, T)] = x match { case SelT(tgt, l) => AM.result((tgt, l))                           case _ => AM.fail("expected SelT") }
  def isRfnT    (x: Any): AM[(Type, RefineMember)] = x match { case RfnT(tgt, cm) => AM.result((tgt, cm))                         case _ => AM.fail("expected RfnT") }
  // isTmpl unrolls self type!
  def isTmpl    (x: Any): AM[(Option[Type], \\[Mems])] = x match { case r@Tmpl(_, body) => AM.result((Some(r.selfType), body))               case _ => AM.fail("expected Tmpl") }
  def isMixT    (x: Any): AM[(Type, Type)] = x match { case MixT(tp1, tp2) => AM.result((tp1, tp2))                       case _ => AM.fail("expected MixT") }
  def isSngl    (x: Any): AM[(Term)] = x match { case Sngl(path) => AM.result((path))                               case _ => AM.fail("expected Sngl") }
  def isUnT     (x: Any): AM[(Type)] = x match { case UnT(un) => AM.result((un))                                    case _ => AM.fail("expected UnT") }
  def isBoxT    (x: Any): AM[(Type)] = x match { case BoxT(t) => AM.result((t))                                    case _ => AM.fail("expected BoxT") }
  def isMemV    (x: Any): AM[(V, Type, Option[Term])] = x match { case MemV(l, classifier, res) => AM.result((l, classifier, res))   case _ => AM.fail("expected MemV") }
  def isMemT    (x: Any): AM[(T, Kind, Option[Type])] = x match { case MemT(l, classifier, res) => AM.result((l, classifier, res))   case _ => AM.fail("expected MemT") }
  def isRMemV   (x: Any): AM[(V, Term)] = x match { case RMemV(l, res) => AM.result((l, res))                          case _ => AM.fail("expected RMemV") }
  def isRMemT   (x: Any): AM[(T, Type)] = x match { case RMemT(l, res) => AM.result((l, res))                          case _ => AM.fail("expected RMemT") }
  def isIn      (x: Any): AM[(Type, Type)] = x match { case In(lower, upper) => AM.result((lower, upper))                 case _ => AM.fail("expected In") }
  def isStruct  (x: Any): AM[(Type)] = x match { case Struct(struct) => AM.result((struct))                         case _ => AM.fail("expected Struct") }
  def isNominalK(x: Any): AM[(Type)] = x match { case NominalK(struct) => AM.result((struct))                       case _ => AM.fail("expected NominalK") }
  def isConcrete(x: Any): AM[(Type)] = x match { case Concrete(struct) => AM.result((struct))                       case _ => AM.fail("expected Concrete") }
  def isUnK     (x: Any): AM[(Kind)] = x match { case UnK(un) => AM.result((un))                                    case _ => AM.fail("expected UnK") }

// case AnyT
// case NothingT

}


      /*case Var(n)
      case SelV(tgt, l)
      case RfnV(tgt, cm)
      case New(tp)
      case SelT(tgt, l)
      case RfnT(tgt, cm)
      case Tmpl(selfTp, body)
      case MixT(tp1, tp2)
      case Sngl(path)
      case AnyT
      case NothingT
      case UnT(un)
      case MemV(l, classifier, res)
      case MemT(l, classifier, res)
      case RMemV(l, res)
      case RMemT(l, res)
      case RMemVX(l, res)
      case RMemTX(l, res)
      case In(lower, upper)
      case Struct(struct)  
      case NominalK(struct)
      case Concrete(struct)
      case UnK(un)    */