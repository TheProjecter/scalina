package scalina
import scala.examples.tcpoly.binding.frescala._

trait Typer { self : Binding with BindingSyntax with Syntax with ScalinaAbsM with Typer with Substitution => 
  import AM._
  
  def ofT(tm: Term, pt: Expected[Type]): AM[Unit] =
      // OfT-Var
      (for(
          (x) <- isVar(tm);
          tp  <- lookup(x);
          _   <- pt := tp)
         
      // OfT-SelPath         
      yield ()) ++ (for(
          (tgt, l) <- isSelV(tm); if tgt.isPath; // tm == p.l
	      tp       <- newMetaTp("T");   // new meta-typevariable
	      x        <- gensym("x");      // new variable
	      _        <- ofT(tgt, Check(Tmpl(None, x \\ Set(MemV(l, tp, None))))); // G |- tgt : {x => val l : tp}   (where tp is unknown)
	      tp       <- !tp;              // retrieve the type tp got unified with
          resTp    <- tp.subst(x, tgt); // [x -> tgt] tp
          _        <- pt := resTp)      // set the result type or check that we inferred the right type (resTp)
         
      // OfT-Sel                      
      yield ()) ++ (for(
          (tgt, l) <- isSelV(tm); if !tgt.isPath;
	      tp       <- newMetaTp("T");
	      x        <- gensym("x");
	      _        <- ofT(tgt, Check(Tmpl(None, x \\ Set(MemV(l, tp, None)))));
	      tp       <- !tp;
                   if tp fresh(x);
          _        <- pt := tp)  

      // OfT-RfnV
      yield ()) ++ (for(
          (tgt, cm) <- isRfnV(tm);
          (l, u)   <- isRMemV(cm);
          tp       <- newMetaTp("T");          
          selfTp   <- newMetaTp("S");          
	      mems     <- newMetaMemsWith("ms", MemV(l, UnT(tp), None));
	      x        <- gensym("x");
	      _        <- ofT(tgt, Check(Tmpl(Some(selfTp), x \\ mems)));
          mems     <- !mems;
	      tp       <- !tp;
          selfTp   <- !selfTp;
                 //  if u fresh(x); // redundant?
          _        <- assume(x, selfTp){
                        ofT(u, Check(tp))
                      };
          _        <- pt := RfnT(Tmpl(Some(selfTp), x \\ mems), cm)) 

      // OfT-RfnT
      yield ()) ++ (for(
          (tgt, cm) <- isRfnV(tm);
          (l, u)   <- isRMemT(cm);
          k        <- newMetaKind("K");          
          selfTp   <- newMetaTp("S");          
	      mems     <- newMetaMemsWith("ms", MemT(l, UnK(k), None));
	      x        <- gensym("x");
	      _        <- ofT(tgt, Check(Tmpl(Some(selfTp), x \\ mems)));
          mems     <- !mems;
	      k        <- !k;
          selfTp   <- !selfTp;
                   //  if u fresh(x); // redundant?
          _        <- assume(x, selfTp){
                        ofK(u, Check(k))
                      };
          _        <- pt := RfnT(Tmpl(Some(selfTp), x \\ mems), cm)) 
    
       // OfT-New
       yield ())++ (for(
          (tp)     <- isNew(tm); if !tp.isInstanceOf[Sngl];
//          rec      = Infer[Type]("R"); 
          rec        <- expand(tp);
//          rec      <- !rec;
          _        <- ofK(rec, Check(Concrete(rec)));
          _        <- pt := tp)
                 
       // OfT-Sing
       yield ())++ (for(
	      x        <- gensym("x");                      
          selfTp   <- newMetaTp("S");          
	      mems     <- newMetaMems("ms");
          if tm.isPath;
          _        <- ofT(tm, Check(Tmpl(Some(selfTp), x \\ mems)));
          mems <- !mems; selfTp <- !selfTp;
          _        <- pt := Sngl(tm))

       // OfT-Subsume
       yield ())++ (for(
          _        <- result(); // dummy TODO: can this be avoided?
          tp       = Infer[Type]("S"); // TODO: add hint that tp should be <: pt ?
          _        <- ofT(tm, tp);
          tp       <- !tp;
          _        <- subT(tp, pt))
                 
       yield ())

  def refine(rec: Tmpl, rmem: RefineMember): AM[Tmpl] = result(null) // TODO
  def refineAll(rec: Tmpl): AM[Tmpl] = result(null) // TODO
  
  def normalise(tp: Type, pt: Expected[Type]): AM[Unit] = 
     (for((t, l)      <- isSelT(tp);
          Tmpl(_, ms)  <- expand(t);
          (x, ms)     <- ms unabs;
          MemT(_, k, Some(s)) <- ms lookup(l);
          if !k.isInstanceOf[NominalK];
          _ <- pt := (s /*subst(x, t) TODO*/)) yield ()) ++ (
            
      for((tp, cm)      <- isRfnT(tp);
          x <- gensym("x"); selfTp <- newMetaTp("S"); mems <- newMetaMems("ms");
          _           <- normalise(tp, Check(Tmpl(Some(selfTp), x \\ mems)));
          mems <- !mems; selfTp <- !selfTp;
          res           <- refine(Tmpl(Some(selfTp), x \\ mems), cm);
          _ <- pt := res) yield ()) ++ (
            
      for((tp1, tp2)    <- isMixT(tp);
           x1 <- gensym("x1"); selfTp1 <- newMetaTp("S1"); mems1 <- newMetaMems("ms1");
           _             <- normalise(tp1, Check(Tmpl(Some(selfTp1), x1 \\ mems1)));
           mems1 <- !mems1; selfTp1 <- !selfTp1;
           x2 <- gensym("x2"); selfTp2 <- newMetaTp("S2"); mems2 <- newMetaMems("ms2");
           _             <- normalise(tp2, Check(Tmpl(Some(selfTp2), x2 \\ mems2)));
           mems2 <- !mems2; selfTp2 <- !selfTp2;
           x             <- gensym("x");
           ms1           <- setTm(mems1) subst(x1, Var(x));
           ms2           <- setTm(mems2) subst(x2, Var(x));
           _ <- pt := Tmpl(Some(selfTp2), x \\ (ms1 ++ ms2))) yield ()) ++ (
      
      for((p)           <- isSngl(tp);
           q             <- newMetaPath("q");
           _             <- ofT(p, Check(Sngl(q)));
           _ <- pt := Sngl(q))
        yield ())
  
  def equal(tp: Type, pt: Expected[Type]): AM[Unit] = 
     // Refl
     (pt := tp) ++ 
     // Norm
     normalise(tp, pt) ++ 
     // Symm
     (for(tp2 <- !pt; 
          _ <- equal(tp2, Check(tp))) yield()) ++
     // Trans
     (for( _ <- result();
        guess = Infer[Type]("T"); // TODO: add hint so that this terminates this century
        _ <- equal(tp, guess);
        guess <- !guess;
        _ <- equal(guess, pt)) yield())
     
  def expand(tp: Type): AM[Tmpl] =
    // Sel
    (for((t, l) <- isSelT(tp);
         Tmpl(_, ms) <- expand(t);
         (x, ms)    <- ms unabs;
         MemT(_, k, Some(s)) <- ms lookup(l);
         res <- expand(s /*subst(x, t) TODO*/)) yield res) ++
    // Rfn
    (for((t, cm) <- isRfnT(tp);
         rec <- expand(t);
         res <- refine(rec, cm)) yield res) ++
    // Refl
    (result(tp) filter{_.isInstanceOf[Tmpl]} map{_.asInstanceOf[Tmpl]}) ++
    // SelfX: implicit
    // Mix
    (for((tp1, tp2)     <- isMixT(tp);
          Tmpl(_, ms1)  <- expand(tp1);
          Tmpl(s2, ms2) <- expand(tp2);
          x             <- gensym("x");
          (x1, ms1)     <- ms1 unabs;
          (x2, ms2)     <- ms2 unabs;
          ms1           <- setTm(ms1) subst(x1, Var(x));
          ms2           <- setTm(ms2) subst(x2, Var(x))) 
       yield Tmpl(s2, x \\ (ms1 ++ ms2))) ++
    // Sing
     (for((p)           <- isSngl(tp);
          t = Infer[Type]("t");
          _             <- ofT(p, t);
          t <- !t;
          r <- expand(t))
       yield r) ++
     // Necsry
     (for((t) <- isBoxT(tp);
          rec <- expand(t);
          res <- refineAll(rec)) yield res)
    
  def subT(tp: Type, pt: Expected[Type]): AM[Unit] = // only place where Expected really makes a difference is rule Interval
     // Refl
     (pt := tp) ++ 
     // Trans
     (for( _ <- result();
        guess = Infer[Type]("T"); // TODO: add hint so that this terminates this century
        _ <- equal(tp, guess);
        guess <- !guess;
        _ <- equal(guess, pt)) yield()) ++
     // Interval
     (pt match {
       case Check(s) => (for(wc <- newMetaTp("_");
                             _ <- ofK(tp, Check(In(wc, s)))) yield ())
       case _ =>  (for(wc <- newMetaTp("_");
                        s <- newMetaTp("s");
                        _ <- ofK(tp, Check(In(wc, s)));
                        s <- !s;
                        _ <- pt := s) yield ())
     }) ++
     // Exp
     (for(r <- expand(tp);
          _ <- pt := r) yield()) ++
     // Eq
     equal(tp, pt) ++
    // Invar
     (pt match {
       case Check(pt) => (for((t1, cm1) <- isRfnT(tp);
                             _ <- isRMemT(cm1);
                             (t2, cm2) <- isRfnT(pt);
                             if cm1 === cm2;
                             _ <- subT(t1, Check(t2))) yield ())
       case _ =>  (for(_ <- pt := tp) yield()) // TODO: can we do better? do we need to?  (mimick checking case, but introduce a new meta variable for t2 (which is constrained so that t1 <: t2)
     }) ++  
    // Struct
     (pt match {
       case Check(pt) => (for((Some(s1), ms1) <- isTmpl(tp);
                              (Some(s2), ms2) <- isTmpl(pt);
                              _ <- subT(s1, Check(s2));
                              (x1, ms1) <- ms1 unabs;
                              (x2, ms2) <- ms2 unabs;
                              // TODO: do this in the AM monad:
                              //ms2 forall {m2 => ms1 exists {m1 => (m1 == m2) && subMem(m1, m2)}}
                              m2 <- results(ms2); // inject N alternatives if ms2 has N elements
                              m1 <- results(ms1); // for every N alternatives, inject M alternatives if ms1 has M elements
                              _ <- if(m1 == m2) subMem(m1, m2) else result(); // for all N*M alternatives, for members with equal labels, check submembering, otherwise succeed directly
                              if ms1 forall {m1 => !m1.deferred || ms2.exists {m2 => (m1 == m2)}} // all un-members in ms1 must have corresponding un-member in ms2
                              ) yield ())
       case _ =>  (for(_ <- pt := tp) yield()) // TODO
     }) ++
     // IElimR
     (pt match {
       case Check(pt) => (for((tp1, tp2)    <- isMixT(tp);
                              Tmpl(_, ms1) <- expand(tp1);
                              Tmpl(_, ms2) <- expand(tp2);
                              (_, ms1)     <- ms1 unabs;
                              (_, ms2)     <- ms2 unabs;
                              if ms2 forall {m2 => !m2.deferred || ms1.exists {m1 => (m1 == m2)}}) yield ())
       case _ =>  (for(_ <- pt := tp) yield()) // TODO
     }) ++
     // IElimL
     (pt match {
       case Check(pt) => (for((tp1, tp2)    <- isMixT(tp);
                              Tmpl(_, ms1) <- expand(tp1);
                              Tmpl(_, ms2) <- expand(tp2);
                              (_, ms1)     <- ms1 unabs;
                              (_, ms2)     <- ms2 unabs;
                              if ms1 forall {m1 => !m1.deferred || ms2.exists {m2 => (m1 == m2)}}) yield ())
       case _ =>  (for(_ <- pt := tp) yield()) // TODO
     }) ++    
     // IIntro
     (pt match {
       case Check(pt) => (for((tp1, tp2)    <- isMixT(pt);
                              _ <- subT(tp, Check(tp1));
                              _ <- subT(tp, Check(tp2))) yield ())
       case _ =>  (for(_ <- pt := tp) yield()) // TODO
     }) ++
     // Any
     (for(_ <- ofK(tp, Infer[Kind]("K"));
          _ <- pt := AnyT) yield ()) ++
     // Nothing
     check(tp eq NothingT) ++
     // Un
     (pt match {
       case Check(pt) => (for((pt) <- isUnT(pt);
                              _    <- subT(pt, Check(tp))) yield ())
       case _ =>  (for(_ <- pt := tp) yield()) // TODO
     })     

  def subMem(mem1: Member, mem2: Member): AM[Unit] =
   // Val
    (for((l1, t1, _) <- isMemV(mem1);
         (l2, t2, _) <- isMemV(mem2);
         if l1 == l2;
         _ <- subT(t1, Check(t2))) yield()) ++
   // Type
    (for((l1, k1, rhs1) <- isMemT(mem1);
         (l2, k2, rhs2) <- isMemT(mem2);
         if l1 == l2 && (rhs2.isEmpty || !rhs1.isEmpty); // mem2 concrete implies mem1 concrete
         _ <- subK(k1, Check(k2))) yield())
          
  def wfMem(mem: Member): AM[Unit] =
   // Val
    (for((l, t, rhs) <- isMemV(mem);
         _ <- rhs match {
           case Some(rhs) => ofT(rhs, Check(t))
           case None => ofK(t, Infer[Kind]("K"))
         }) yield()) ++
   // Type
    (for((l, k, rhs) <- isMemT(mem);
         _ <- rhs match {
           case Some(rhs) => ofK(rhs, Check(k))
           case None => wfKind(k)
         }) yield()) 
             
  def ofK(tp: Type, pk: Expected[Kind]): AM[Unit] =
    // Struct
    (for((Some(s), ms) <- isTmpl(tp);
         (x, ms) <- ms unabs;
         _ <- assume(x, s)(for(m <- results(ms);
                               _ <- wfMem(m)) yield ());
         _ <- pk := Struct(tp)) yield ()) ++ (
    // Mix
     for((tp1, tp2)     <- isMixT(tp);
          x1 <- gensym("x1"); selfTp1 <- newMetaTp("S1"); mems1 <- newMetaMems("ms1");
          _ <- ofK(tp1, Check(Struct(Tmpl(Some(selfTp1), x1 \\ mems1))));
          mems1 <- !mems1; selfTp1 <- !selfTp1;
          x2 <- gensym("x2"); selfTp2 <- newMetaTp("S2"); mems2 <- newMetaMems("ms2");
          _ <- ofK(tp2, Check(Struct(Tmpl(Some(selfTp2), x2 \\ mems2))));
          mems2 <- !mems2; selfTp2 <- !selfTp2;
          _ <- subT(selfTp2, Check(selfTp1));
          m2 <- results(mems2); // inject N alternatives if ms2 has N elements
          m1 <- results(mems1); // for every N alternatives, inject M alternatives if ms1 has M elements
          _ <- if(m1 == m2) subMem(m1, m2) else result(); // for all N*M alternatives, for members with equal labels, check submembering, otherwise succeed directly
          x             <- gensym("x");
          mems1         <- setTm(mems1) subst(x1, Var(x));
          mems2         <- setTm(mems2) subst(x2, Var(x));
          _ <- pk := Struct(Tmpl(Some(selfTp2), x \\ (mems1 ++ mems2)))
         ) yield()) ++ (
    // Concrete
     for(x <- gensym("x"); S <- newMetaTp("S"); MS <- newMetaMems("MS");
          _ <- ofK(tp, Check(Struct(Tmpl(Some(S), x \\ MS))));
         S <- !S; MS <- !MS; 
         _ <- subT(BoxT(tp), Check(S));
         m <- results(MS);
         if m.nonAbstract; 
         _ <- pk := Concrete(Tmpl(Some(S), x \\ MS))
         ) yield()) ++ (
     // Sing
     for((p) <- isSngl(tp);
         t = Infer[Type]("T");
         _ <- ofT(p, t); t <- !t;
         R <- newMetaTp("R");
         _ <- ofK(t, Check(Struct(R))); R <- !R;
         _ <- pk := Concrete(R)
        ) yield()) ++ (
     // SelPath
     for((tgt, l) <- isSelT(tp); 
         (p)      <- isSngl(tgt);
	      k       <- newMetaKind("K");   // new meta-kindvariable
	      x        <- gensym("x");      // new variable
	      _        <- ofK(tgt, Check(Concrete(Tmpl(None, x \\ Set(MemT(l, k, None)))))); // G |- tgt : {x => type L : K}   (where K is unknown)
	      k        <- !k;              // retrieve the kind k got unified with
          res      <- k.subst(x, p); // [x -> p] K
          _        <- pk := res      // set the result kind or check that we inferred the right kind
      ) yield()) ++ (
      // Sel
     for((tgt, l) <- isSelT(tp); 
	      k       <- newMetaKind("K");   // new meta-kindvariable
	      x        <- gensym("x");      // new variable
	      _        <- ofK(tgt, Check(Concrete(Tmpl(None, x \\ Set(MemT(l, k, None)))))); // G |- tgt : {x => type L : K}   (where K is unknown)
	      k        <- !k;              // retrieve the kind k got unified with
          if k fresh(x);
          _        <- pk := k      // set the result kind or check that we inferred the right kind
      ) yield()) ++ (
      // RfnV
      for((tgt, cm) <- isRfnT(tp);
          (l, u)    <- isRMemV(cm);
	      x        <- gensym("x");
          tp       <- newMetaTp("T"); selfTp   <- newMetaTp("S");          
	      mems     <- newMetaMemsWith("ms", MemV(l, UnT(tp), None));
	      _        <- ofK(tgt, Check(Struct(Tmpl(Some(selfTp), x \\ mems))));
	      tp       <- !tp; selfTp <- !selfTp; mems <- !mems;
          _        <- assume(x, selfTp){
                        ofT(u, Check(tp))
                      };
          rec      <- refine(Tmpl(Some(selfTp), x \\ mems), cm);
          _        <- pk := Struct(rec)) yield ()) ++ (
      // RfnT
      for((tgt, cm) <- isRfnT(tp);
          (l, u)    <- isRMemT(cm);
	      x        <- gensym("x");
          k       <- newMetaKind("K"); selfTp   <- newMetaTp("S");          
	      mems     <- newMetaMemsWith("ms", MemT(l, UnK(k), None));
	      _        <- ofK(tgt, Check(Struct(Tmpl(Some(selfTp), x \\ mems))));
	      k       <- !k; selfTp <- !selfTp; mems <- !mems;
          _        <- assume(x, selfTp){
                        ofK(u, Check(k))
                      };
          rec      <- refine(Tmpl(Some(selfTp), x \\ mems), cm);
          _        <- pk := Struct(rec)) yield ()) ++ (
      // Subsume
      for(_        <- result(); // dummy TODO: can this be avoided?
          k1       = Infer[Kind]("K1"); // TODO: add hint that tp should be <: pt ?
          _        <- ofK(tp, k1);
          k1       <- !k1;
          _        <- subK(k1, pk)) yield ()) ++ (
      // Any
      for(x <- gensym("x");
          if tp eq AnyT;
          _ <- pk := Struct(Tmpl(None, x \\ Set()))) yield ()) ++ (
      // Nothing
      for(x <- gensym("x");
          if tp eq NothingT;
          _ <- pk := Struct(Tmpl(None, x \\ Set()))) yield ()) ++ (
      // Un
      for((t) <- isUnT(tp);
          _ <- ofK(t, Infer[Kind]("K"));
          x <- gensym("x");
          _ <- pk := Struct(Tmpl(None, x \\ Set()))) yield ()) 
  
  def subK(k: Kind, pk: Expected[Kind]): AM[Unit] =
    // Un
    (for((k1) <- isUnK(k);
        _ <- pk match {
		      case Check(pk) => for((k2) <- isUnK(pk);
                                    _ <- subK(k2, Check(k1))) yield ()
              case _ =>  pk := k // TODO
		    }) yield ()) ++ (
    // Nom
    for((r1) <- isNominalK(k);
    _ <- pk match {
	      case Check(pk) => for((r2) <- isStruct(pk);
                                if r1 === r2) yield () // TODO: use equal?
          case _ =>  pk := Struct(r1) // TODO
	    }) yield ())  ++ (
    // Conc
    for((r1) <- isConcrete(k);
         _ <- pk match {
	      case Check(pk) => for((r2) <- isStruct(pk);
                                if r1 === r2) yield () // TODO: use equal?
          case _ =>  pk := Struct(r1) // TODO
	    }) yield ()) ++ (
    // Struct
    for((r) <- isStruct(k);
         _ <- pk match {
	      case Check(pk) => for((s, t) <- isIn(pk);
                                _ <- subT(s, Check(r));
                                _ <- subT(r, Check(t))) yield () // TODO: use equal?
          case _ => for(s <- newMetaTp("S");
                        t = Infer[Type]("T");
                        _ <- subT(s, Check(r)); s <- !s;
                        _ <- subT(r, t); t <- !t;
                        _ <- pk := In(s, t)) yield ()
	    }) yield ()) ++ (
    // Ctx-Conc
    for((r1) <- isConcrete(k);
         _ <- pk match {
	      case Check(pk) => for((r2) <- isConcrete(pk);
                                _ <- subT(r1, Check(r2))) yield () 
          case _ =>  for(_ <- result();
                         r2 = Infer[Type]("R2");
                         _ <- subT(r1, r2); r2 <- !r2;
                         _ <- pk := Concrete(r2)) yield ()
	    }) yield ()) ++ (
    // Ctx-Struct
    for((r1) <- isStruct(k);
         _ <- pk match {
	      case Check(pk) => for((r2) <- isStruct(pk);
                                _ <- subT(r1, Check(r2))) yield () 
          case _ =>  for(_ <- result();
                         r2 = Infer[Type]("R2");
                         _ <- subT(r1, r2); r2 <- !r2;
                         _ <- pk := Struct(r2)) yield ()
	    }) yield ()) ++ (
    // Ctx-In
    for((t1, t2) <- isIn(k);
         _ <- pk match {
	      case Check(pk) => for((s1, s2) <- isIn(pk);
                                _ <- subT(t2, Check(s2));
                                _ <- subT(s1, Check(t1))) yield () 
          case _ =>  for(s1 <- newMetaTp("S1");
                         s2 = Infer[Type]("S2");
                         _ <- subT(t2, s2); s2 <- !s2;
                         _ <- subT(s1, Check(t1)); s1 <- !s1;
                         _ <- pk := In(s1, s2)) yield ()
	    }) yield ()) 
    
  def wfKind(k: Kind): AM[Unit] = result() // TODO
  //def wfGamma(env: Gamma): AM[Unit] 

}

// TODO: write small test to see if this actually works (i.e., bind variable x to a structural type with one member l and then type x.l) 
object Test extends ScalinaAbsM with BindingSyntax with Binding with Substitution with Syntax with Typer with Application {
  import AM._
  
  // Expected output: Some(Success(AnyT))
  println((for(x <- gensym("x");
      self <- gensym("self");
      tp <- assume(x, Tmpl(None, self \\ Set(MemV(V('a), AnyT, None))))(for( // Gamma = x: {self => val a: Any}
          _ <- result(); // need a _ <- ... before we can do tpInfer = ... ?
          tpInfer = Infer[Type]("T");
          _ <- ofT(SelV(Var(x), V('a)), tpInfer); // Gamma |- x.a : tpInfer
          tpInfer <- !tpInfer
        ) yield tpInfer) 
      ) yield tp).run)
  
  // Expected output: Some(Success(RfnT(Tmpl(Some(Unrolled(Tmpl(None,\\@e33e18))),\\@642bd6),RMemV(V('a),Var(y$2)))))
  println((for(x <- gensym("x"); y <- gensym("y");
      self <- gensym("self");
      tp <- assume(x, Tmpl(None, self \\ Set(MemV(V('a), UnT(AnyT), None))))(for( // Gamma = x: {self => val a: Un[Any]}
          _ <- result(); // need a _ <- ... before we can do tpInfer = ... ?
          tpInfer = Infer[Type]("T");
          _ <- assume(y, AnyT)(ofT(RfnV(Var(x), RMemV(V('a), Var(y))), tpInfer)); // Gamma, y: AnyT |- x.a : tpInfer 
          tpInfer <- !tpInfer
        ) yield tpInfer) 
      ) yield tp).run)  

}