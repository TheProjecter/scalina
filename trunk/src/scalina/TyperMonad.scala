package scalina

import scala.examples.tcpoly.monads._
import scala.examples.tcpoly.binding.frescala._

class ScalinaAbsM extends AbsM { self : Binding with BindingSyntax with Syntax with ScalinaAbsM  => 
  type Tag = Int

  // deep equality that also does unification of MetaVar's 
  trait CheckingEquality[A] extends Equality[A] {
    def ===(other: A): Boolean
  }
  
  implicit def OptionCEq[T <% CheckingEquality[T]](self: Option[T]): CheckingEquality[Option[T]] = new CheckingEquality[Option[T]] {
    def ===(other: Option[T]): Boolean = (for( s <- self; o <- other) yield s === o) getOrElse(true)
  }

  implicit def NameCEq(self: Name): CheckingEquality[Name] = new CheckingEquality[Name] {
    def ===(other: Name): Boolean = self == other
  }
  
  implicit def AbsCEq[T <% CheckingEquality[T]](x: \\[T]): CheckingEquality[\\[T]] = new CheckingEquality[\\[T]] {
      def ===(a: \\[T]): Boolean = x.gequals[CheckingEquality](a)
  }

  // facilities for bidirectional type checking (logic programming, really)
  abstract class Expected[A <% CheckingEquality[A]] {
    def :=(tp: A): AM[Unit]
    def unary_! : AM[A]
  }

  def Infer[A <% CheckingEquality[A]](n: String): Infer[A] = new Infer[A](n: String)
  class Infer[A <% CheckingEquality[A]](val name: String) extends Expected[A] {
    private var tp: Option[A] = None 
    def :=(tp: A): AM[Unit] = AM.result(this.tp=Some(tp))
    def unary_! = tp map {AM.result(_)} getOrElse AM.fail("inference of "+name+" failed")
  }
  
  case class Check[A <% CheckingEquality[A]](val tp: A) extends Expected[A] {
    def :=(tp: A): AM[Unit] = 
      if(this.tp === tp) {
        println("check: "+this.tp+" == "+tp)
        AM.result(()) 
      } else {
        println("check: "+this.tp+" != "+tp)
        AM.fail("type checking failed") 
      }
    def unary_! = AM.result(tp)
  }
  
  // results of the monad
  sealed abstract class Result[A] extends Monad[A, Result] {
    object meta extends MonadCompanion[Result]{
      implicit def result[A](x: A) = Success(x)
    }
    def filter(pred: A => Boolean): Result[A]     
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B]
  } 
  
//  def Success[A](r: A): Success[A] = Success(r, List())
  
  // TODO: generalise res to deal with multiple results (Stream / List)
  case class Success[A](res: A) extends Result[A] {
    def >>=[B](next: A => Result[B]) = next(res) //concat (more map ((mo: () => Result[A]) => () => mo() >>= next))
    def filter(pred: A => Boolean): Result[A] = if(pred(res)) this else Failure("filtered out")
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B] = f(res)
  }
  
  case class Failure[A](msg: String) extends Result[A] {
    def >>=[B](next: A => Result[B]) = Failure[B](msg)
    def filter(pred: A => Boolean): Result[A] = this
    def mapOutZero[M[_], B](f: A => M[B])(z: Result[B] => M[B]): M[B] = z(Failure[B](msg))
  }
  
  // state that is carried along
  case class AbsState(currTag: Int) {
    def next = AbsState(currTag+1)
  }
  
  // environment that is available
  type Gamma = Map[Name, Type]
  case class AbsEnv(gamma: Gamma) {
    def extend(vr: Name, tp: Type): AbsEnv = AbsEnv(gamma + vr -> tp)
  }
  
  // meta variable used by the type checker
  trait MetaVar[T] extends CheckingEquality[T] { self: T with MetaVar[T] =>
    val tag: Tag
    val name: String
    var v: Option[T]
    
    def swap(a: Name, b: Name) = this
    def fresh(a: Name) = true
    def supp = List()
    
    // if this variable unifies with o, return Some(o)  -- TODO: use dependent method type Option[o.type]
    def unifies(o: T): Option[T]
    
    def unify(o: T): Boolean = {
      assert(v.isEmpty)
      println("unified "+this+" to "+o)
      v = unifies(o)
      !v.isEmpty
    }
    
    def unary_! = v map {AM.result(_)} getOrElse AM.fail("meta variable "+name+" not set")
    
    // if set, check against that -- if not set, unify with o and return true
    override def ===(o: T) = // v map{_ === o} getOrElse(unify(o))
      v match { 
        case Some(v) => !unifies(v).isEmpty
        case None => unify(o) 
      }  
    
  }
  
  type AMFun[A] = From => To[A]
  
  implicit object AM extends AbsMonadCompanion {
    def apply[A](f: AMFun[A]): AM[A] = new AM(f)
    
    // inject x into the monad
    def result[A](x: A) = AM{_ mapEnvTo(_y => Success(x))}
    def results[A](x: Iterable[A]): AM[A] = AM{ case From(st, env) => To(Stream.fromIterator(x.elements) map {x => (st, Success(x))})}
    def fail[A](msg: String) = AM{_ mapEnvTo(_y => Failure[A](msg))}

    def check(p: => Boolean) = result() filter(x => p)

    // create a fresh tag and return it
    def newTag: AM[Tag] = AM{_ mapStateTo(_.next, st => Success(st.currTag)) }    
   
    def newMetaPath(n: String) = newMetaTerm(n, false, true)
    def newMetaTerm(n: String, isValue: Boolean, isPath: Boolean): AM[MetaTerm] = for(t <- newTag) yield MetaTerm(isValue, isPath, t, n, None)    
    def newMetaTp(n: String): AM[MetaTp] = for(t <- newTag) yield MetaTp(t, n, None)
    def newMetaKind(n: String): AM[MetaKind] = for(t <- newTag) yield MetaKind(t, n, None)
    def newMetaMems(n: String): AM[MetaMems] = for(t <- newTag) yield MetaMems(Set(), t, n, None)
    def newMetaMemsWith(n: String, m: Member): AM[MetaMems] = for(t <- newTag) yield MetaMems(Set(m), t, n, None)
    
    def assume[A](vr: Name, tp: Type)(in: AM[A]): AM[A] = AM{x =>
      in(x mapEnv {_.extend(vr, tp)})
    }
    
       
    def getGamma: AM[Gamma] = AM{_ mapEnvTo(x => Success(x.gamma)) }
    
    def lookup(n: Name): AM[Type] = getGamma >>= {
      _.get(n) match {
	    case Some(t) => println("lu"+t); result(t)
	    case None => fail("")
      }
    }
  }
  
  object initState extends AbsState(0)
  object initEnv extends AbsEnv(Map())

  type TResult[A] = Option[Result[A]]

  class AM[A](val fun: AMFun[A]) extends AMFun[A] with Monad[A, AM] {
    def apply(x: From) = fun(x)
    val meta = AM ; import meta._
  
    def filter(pred: A => Boolean): AM[A] = AM{x => this(x) filterRes(pred)}
      
    // chains this computation with the next one
    def >>=[B](next: A => AM[B]): AM[B] = AM{x => this(x) chainRes((st, r) => next(r)(x.state = st), To(_, _))}
	  
    def ++(alt: => AM[A]): AM[A] = AM{x => this(x) ++ alt(x) }
    
    def findAll = this(From(initState, initEnv)).tos map {case (st, r) => r} toList
    def run = this(From(initState, initEnv)).tos map {case (st, r) => r} find{case Success(_) => true; case _ => false}
  } 

    
  case class From(st: AbsState, env: AbsEnv) { // current state and environment
    def state = st
    def state_= (newSt: AbsState) = From(newSt, env) // why can't I name this st_= ?
    def mapEnv(f: AbsEnv => AbsEnv) = From(st, f(env))
    def mapEnvTo[A](f: AbsEnv => Result[A]) = To(st, f(env))
    def mapStateTo[A](next: AbsState => AbsState, f: AbsState => Result[A]) = {val n = next(st); To(n, f(n))}
  }
  
  def To[A](st: AbsState, r: Result[A]): To[A] = To(Stream.fromIterator(List((st, r)).elements))
  case class To[A](tos: Stream[(AbsState, Result[A])]) { // next state and result
    def filterRes(pred: A => Boolean) = mapRes(_.filter(pred))

    // if non-zero, compute the next state every element
    // zero: return zero (default element, can't be computed using the previous function)      
    def chainRes[B](f: (AbsState, A) => To[B], z: (AbsState, Result[B]) => To[B]): To[B] =
      mapStRes{case (st, r) => r.mapOutZero[To, B](x => f(st, x))(x => z(st, x))} 

    def mapRes[B](f: Result[A] => Result[B]): To[B] = To(tos map {case (st, r) => (st, f(r))})
    def mapStRes[B](f: (AbsState, Result[A]) => To[B]): To[B] = To(tos.flatMap {case (st, r) => f(st, r).tos})
    def ++(alt: => To[A]): To[A] = To(tos append alt.tos)
  }
  
  def sequence[T](s: Option[AM[T]]): AM[Option[T]] = error("TODO") 
  def sequence[T](s: Set[AM[T]]): AM[Set[T]] = error("TODO")

}
