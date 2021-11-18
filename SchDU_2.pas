unit SchDU_2;

interface

uses math, Dialogs, SysUtils;

type float = extended;
type v10 = ARRAY[1..10] OF float;
     vec2 = array [1..2] of float;
     matr3_3 = array [1..3,1..3] of float;


function ConvToRound(x: float): float;
Procedure PConvToRound(var x: float);

procedure AgecoToKepler(x, y, z, Vx, Vy, Vz:  float;
                    out p, e, i, OmB, teta, OmM: float);
procedure KeplerToAgeco( p, e, i, OmB, teta, OmM: float;
                     out x, y, z, Vx, Vy, Vz:  float);

function calcTet(tet1, e1, p1, e2, p2: float):float;
function calcDT(p, e, t0, t1, t_imp:float):float;
procedure PrivUgla(var ugol: float);


procedure KeoToNewKeo(p0, e0, i0, Omb0, Omm0, teta0, dvr, dvn, dvb:float;
                      out p, e, i, Omb, Omm, teta: float); overload;
procedure KeoToNewKeo(p0, e0, i0, Omb0, Omm0, dvr, dvn, dvb,
                      pk, ek, ik, Ombk, Ommk:float;
                      out p, e, i, Omb, Omm: float;
                      var tetak, teta0: float); overload;



procedure OptOrbToOrb(ArgP_u, ArgP_k, Fpar_u, Fpar_k, Exsc_u, Exsc_k,
                      Vosh_u, Vosh_k, Nakl_u, Nakl_k: float;
                      out Anom_u, Anom_k, DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a: float);





PROCEDURE PLT_2I(ArgP_u, Anom_u, ArgP_k, Anom_k, Fpar_u, Fpar_k, Exsc_u, Exsc_k,
                 Vosh_u, Vosh_k, Nakl_u, Nakl_k: float;

                 out DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a: float );

 (*     Расчет двухимпульсного перелета
  ArgP_u, Anom_u - аргумент перигея и истинная аномалия исходной орбиты, град
  ArgP_k, Anom_k - аргумент перигея и истинная аномалия конечной орбиты, град
  Fpar_u, Fpar_k - фокальный параметр, км.
  Exsc_u, Exsc_k - эксцентриситет нач. и исх. орб.
  Vosh_u, Vosh_k - прямое восхождение, град
  Nakl_u, Nakl_k - наклонение, град
 *)





PROCEDURE By_Imp(p0, e0, w0, i0, Om0, tt0,
                 pk, ek, wk, ik, Omk, ttk : float;

                 var dV1, dVr1, dVn1, dVb1,
                     dV2, dVr2, dVn2, dVb2,     dVsum, fi : float);







  Procedure point_const(p0, e0, w0, i0, Om0, tt0,
                      pk, ek, wk, ik, Omk, tt1, C, D, chag1, cf_max : float;
                      var ttsr, dVmin : float);


//  PROCEDURE  N360(VAR a:float);

  PROCEDURE VZLET(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k: float;
            out DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a: float);

//  FUNCTION  ATN360(s,c:float):float;

  PROCEDURE KOEFF(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k: float;
                out Vr_u{m/c}, Vr_k, Vn_u, Vn_k: float); overload;

  PROCEDURE KOEFF(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k,
                sin_D, cos_D, cos_A1, cos_A2: float;
                out F_u, F_k, a, b, c, d, e, f, Vr_u{m/c}, Vr_k, Vn_u, Vn_k: float); overload;

  PROCEDURE KVADRA(VAR a, b, c, d, e:float; VAR ind:INTEGER; out x, y, XRe: v10);

  PROCEDURE FOKPAR(cos_D, sin_D, modR_u, modR_k, Bpol: float; out q1, q2: float);

  PROCEDURE IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
                 F_u, F_k, Vn_u, Vn_k, Vr_k: float;

             out a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k: float);

//  PROCEDURE POLUOS(q, cos_D, sin_D, modR_u, modR_k: float; out  Bpol: float);

// LibKepl  begin
//  Function  EEE   (    tt,exs:float):float;
//  Function  HHH   (    tt,exs:float):float;
//  Function  TTT   (    p,ex,tt0,t0,t:float):float;
  Function  TVSTR (    tt0,tt1,p,exs:float):float;
//  Function  TETT  (    p,r,exs,Q:float):float;

//  Function  Tper  (    v0,q0,r0,fi:float):float;

  Procedure RVQpl(vxk,xye,wxzd,uvxk,ivye,oMvzd:float;
                  Var R0,V0,Q0,
                  xkn,yen,zdn,vxkn,vyen,vzdn, {-нормализованные }
                                        { параметры R0,V0 }
                   A1,B1,C1,K1 :float); {Параметры пл. начального эллипса }
                                          {в норм. виде                     }
  Procedure RVQ0(      pri:byte;
                       xi,yp,ze,Vxw,VyOmb,Vzu:float;
                   var R0,V0,Q0:float);
  Procedure TAU(q0, r0, r1, fi: float; var DT, V0: float);
  Procedure KEP   (    xk,ye,zd,vxk,vye,vzd:float;
                   var i,p,e,w,te0,u0,ci,si,soMb,coMb,somm,comm,
                       ste0,cte0,su0,cu0:float);
  Function  Psi_t  (psi_max,tn,tk,ti,t : float) : float;
  Procedure Kep_Par(x,y,z,vx,vy,vz : float; var i,omb,p,e,omm,u : float);
  Procedure Toch_per(om,om_op,it,i_op:float;var fi,fi_op,c:float);
  Procedure XYZ(r,u,si,ci,sOm,cOm : float; var x,y,z : float);
   FUNCTION  PTAN(s,c:EXTENDED):EXTENDED;
  Function  Gamma(mx,my,mz,nx,ny,nz,x,y,z : float) : float;
  Function  VIP(f1,f2,f3:float):integer;
// LibKepl  end


implementation
 uses ParamOG;

type func1 = function(x:float) : float;

Const b00 = 398600.44e9; //m3\c2
var    Naklonenie: float;



PROCEDURE  N360(VAR a:float);
 {---------------------------}
   (*  Нормализация угла в пределах  0 % 360 град. *)
BEGIN
    WHILE a<0.0   DO a := 360.0 + a;
    WHILE a>360.0 DO a := a - 360.0
END; (* Конец процедуры  N360 *)


//-------------------------------------------------------------------------
PROCEDURE  N180(VAR a:float);
     {---------------------------}
       (*  Нормализация угла в пределах  -180 % 180 град. *)
BEGIN
    WHILE a<(-180.0) DO a := 360.0 + a;
    WHILE a>180.0    DO a := a - 360.0
END; (* Конец процедуры  N180 *)

//-------------------------------------------------------------------------
FUNCTION  SINH(a :float) :float;
  {---------------------------}
  (* Гиперболический косинус*)
BEGIN
      sinH := ( EXP(a) - EXP(-a))/2.0
END;

//-------------------------------------------------------------------------
FUNCTION  COSH(a :float) :float;
  {---------------------------}
  (* Гиперболический косинус*)
BEGIN
      COSH:=(EXP(a) + EXP(-a))/2.0
END;


//-------------------------------------------------------------------------
FUNCTION  ATANH(a:float):float;
 {----------------------------}
 (*  Арктангенс гиперболический *)
BEGIN
     ATANH:=0.0;
     IF ABS(a) < 1.0 THEN
       ATANH:=(LN( (1.0 + a)/(1.0 - a) ) )/2.0
     ELSE
       ATANH:=(LN( (1.0 + a)/(a - 1.0) ) )/2.0
END; (* Конец функции ATANH *)

//-------------------------------------------------------------------------
FUNCTION  ATN360(s, c:float):float;
  {-------------------------------}
    (*  Арктангенс в пределах  0 % 360 град. SIN=s, COS=c *)
   VAR a:float;
BEGIN
   A := radtodeg(arctan2(s, c));
   if A<0 then ATN360 := A + 360
          else ATN360 := A;
END;  (*  Конец функции  ATN360  *)


//-------------------------------------------------------------------------
FUNCTION  PTAN(s,c:EXTENDED):EXTENDED;
 {--------------------------------------}
   (*  Арктангенс в пределах  0 % 2*PI SIN=s, COS=c *)
   VAR a:EXTENDED;
BEGIN
   A := arctan2(s, c);
   if A<0 then PTAN := A + 2*pi
          else PTAN := A;
END;  (*  Конец функции  PTAN  *)


//-------------------------------------------------------------------------
FUNCTION  ATN180(s,c:float):float;
  {-------------------------------}
    (*  Арктангенс в пределах   -180 % 180 град. SIN=s, COS=c *)
BEGIN
   ATN180 := radtodeg(arctan2(s, c));
END;  (*  Конец функции  ATN180   *)


//-------------------------------------------------------------------------
PROCEDURE  KUB(VAR a,b,c,d:EXTENDED; VAR ind:INTEGER; out y:v10);
 {-----------------------------------------------------}
 (*          Решение кубических уравнений вида :             *)
 // var     y : array [1..6] of float;
 (*        a*(y)**3 + b*(y)**2 + c*(y) + d = 0               *)
  LABEL 10;
VAR dd,dp,r,s,t,p,q,rr,dr,h,g,hg:EXTENDED;
       f,ch,th,sh,f0,dfdy,dy1,dy2:EXTENDED;
                                  i,k,j:INTEGER;

BEGIN           (*   НАЧАЛО  *)
   IF a<1.0E-20 THEN BEGIN
//      MessageDlg('KUB Уравнение является вырожденным: a=0', mtInformation,[mbOk], 0);
      GOTO 10
    END;

    r := b/a;
    s := c/a;
    t := d/a;
    ind  := 2;
    y[2] := 0.0;
    p    := s - sqr(r)/3.0;
    q    := sqr(r)*r/13.5 - r*s/3.0 + t;

    IF ABS(q)<1.0E-50 THEN BEGIN
//      MessageDlg('KUB:   ошибка: при решении ур-ия 4-й степени должно быть q<>0;  q= '+floattostr(q), mtInformation,[mbOk], 0);

      FOR i := 1 TO 6 DO y[i] := 0.0;

      f:=SQRT(ABS(p));

      IF p < 0.0 THEN y[3] := f
                 ELSE y[4] := f;

      y[5] := -y[3];         y[6] := -y[4];
      r    := r/3.0;         y[1] := y[1] - r;   //y[1]==0!!!!!!!!!!!!!!!!!!!!!!!
      y[3] := y[3] - r;      y[5] := y[5] - r;   //y[5]==0!!!!!!!!!!!!!!!

      GOTO 10
    END;

    dp := p/3.0;
    dd := sqr(dp)*dp + sqr(q/2.0);
    rr := SIGN(q) * SQRT( ABS(p)/3.0 );
    hg := q/2.0/sqr(rr)/rr;

    IF p>0.0 THEN BEGIN
       ind := 2;
       ch  := SQRT(1.0 + sqr(hg));
       th  := hg/ch;
       f   := ATANH(th);
       dp  := f/3.0;
       ch  := COSH(dp);
       sh  := SINH(dp);
       y[3]:= rr*sh;
       y[1]:= -2.0*y[3];
       y[4]:= SQRT(3.0)*rr*ch;
       y[5]:= y[3];
       y[6]:= -y[4];
    END
    ELSE IF dd>0.0 THEN BEGIN
       ind:=2;

       IF ABS(hg)< 1.0 + 1.0E-30 THEN sh := 0.0
                                 ELSE sh := SQRT( sqr(hg) - 1.0 );
       th := sh/hg;
       f  := ATANH(th);
       dp := f/3.0;
       ch := COSH(dp);
       sh := SINH(dp);
       y[3] :=  rr*ch;
       y[1] := -2.0*y[3];
       y[4] :=  SQRT(3.0)*rr*sh;
       y[5] :=  y[3];
       y[6] := -y[4];
    END
    ELSE BEGIN
       ind:=4;

       IF ABS(hg) > 1.0-1.0E-30 THEN f := 0.0
       ELSE BEGIN
          sh := SQRT(1.0 - sqr(hg));
          th := sh/hg;
          f  := ARCTAN(th)/3.0;
       END;

       dr := -2.0*rr;
       y[4] := 0.0;
       y[6] := 0.0;
       y[1] := dr*COS(f);
       y[3] := dr*COS(f+PI/1.5);
       y[5] := dr*COS(f+PI/0.75);
    END;

    r := r/3.0;
    y[1] := y[1] - r;
    y[3] := y[3] - r;
    y[5] := y[5] - r;

    IF (ind=4) AND (y[1]*y[3]*y[5]<0) THEN BEGIN
       IF (y[1]<0) AND (ABS(y[1])<1.0E-6) THEN y[1] := 1.0E-10;
    END;

    IF (ind=4) AND ((y[1]<0.0) OR (y[3]<0.0)) THEN ind:=0;

    10: ;
END; (* Конец процедуры KUB *)
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

PROCEDURE KVADRA(VAR a, b, c, d, e:float; VAR ind:INTEGER; out x, y, XRe: v10);
  (* Вычисление корней 4-й степени: результат содержится в    *)
  // глобальная переменная y: array[1..] of float;
  (* векторе Х[1..8], ind - количество действительных корней. *)
  (* Действительные корни содержатся в векторе XRe[1..4]      *)
LABEL 1,2;

VAR p, q, r, s, t, ss, aa, ff, dd,
    f0, f1, f2, f3, pr, xx, dx: float;
    z:       ARRAY[1..6] of float;
    f, g, h: ARRAY[1..2] of float;
    w:       ARRAY[1..4,1..3] OF INTEGER;
    i, j, k, l: INTEGER;

    { извлечение корня из комплексного числа (f[1]'f[2]);
     результат - комплексное число (g[1],g[2]) }
   PROCEDURE CQRT;
   CONST st=1.0e-50;
   VAR aa, ss, ff, c: EXTENDED;
                   k: INTEGER;
   BEGIN
      aa := SQRT(sqr(f[1]) + sqr(f[2]));

      IF aa < st THEN FOR k := 1 TO 2 DO g[k]:=0.0;

      c  := f[1]/aa;
      ss := f[2]/aa;
      aa := SQRT(aa);

      IF ABS(c)<st THEN ff := SIGN(ss)*pi/4.0
                   ELSE ff := PTAN(ss,c)/2.0;

      IF ABS(ss)<st THEN ff := pi/4.0*(1.0 - SIGN(c));

      g[1] := aa*COS(ff);
      g[2] := aa*SIN(ff);
   END; { cqrt }
   //-----------------------------------------

begin
   if (abs(b)<1.0e-20) and (abs(d)<1.0e-20) then begin
      ind  := 0;
      y[1] := -1.0;
      dd   := sqr(c) - 4.0*a*e;

      if dd>0.0 then begin
         dd   := sqrt(dd);
         h[1] := (-c+dd)/2.0/a;
         h[2] := (-c-dd)/2.0/a;
         ss   := sqrt(abs(h[1]));

         if h[1]>0.0 then begin
            ind := ind + 2;
            x[1] := ss;
            x[2] := 0.0;
            x[3] := -ss;
            x[4] := 0.0;
         end
         else begin
            x[1] := 0.0;
            x[2] := ss;
            x[3] := 0.0;
            x[4] :=-ss;
         end;
         ss := sqrt(abs(h[2]));

         if h[2]>0.0 then begin
            ind  := ind+2;
            x[5] := ss;
            x[6] := 0.0;
            x[7] := -ss;
            x[8] := 0.0;
         end
         else begin
            x[5] := 0.0;
            x[6] :=  ss;
            x[7] := 0.0;
            x[8] := -ss;
         end;
      end

      else begin
         f[1] := -c/2.0/a;
         f[2] := sqrt(-dd)/2.0/a;

         cqrt;

         x[1] := g[1];         x[2] := g[2];
         x[3] := g[1];         x[4] :=-g[2];
         f[2] :=-f[2];

         cqrt;

         x[5] := g[1];         x[6] := g[2];
         x[7] := g[1];         x[8] :=-g[2];
      end;
   end

   else begin
      w[1,1] := 1;        w[1,2] := 1;        w[1,3] := 1;
      w[2,1] := 1;        w[2,2] :=-1;        w[2,3] :=-1;
      w[3,1] :=-1;        w[3,2] := 1;        w[3,3] :=-1;
      w[4,1] :=-1;        w[4,2] :=-1;        w[4,3] := 1;

      p := ( 8.0*a*c - 3.0*sqr(b) ) /8.0 /sqr(a);
      q := ( 8.0*sqr(a)*d - 4.0*a*b*c + sqr(b)*b ) /8.0 /a /sqr(a);
      r := ( 256.0*sqr(a)*a*e - 64.0*sqr(a)*b*d + 16.0*a*sqr(b)*c - 3.0*sqr(sqr(b)) ) /256.0 /sqr(sqr(a));
      t := -sqr(q);
      s := sqr(p) - 4.0*r;
      r := 2.0*p;
      aa := 1.0;

      for i := 1 to 4 do XRe[i]:=0.0;

      KUB(aa, r, s, t, ind, y);

      z[1] := sqrt(abs(y[1]));
      z[2] := 0.0;

      if y[1]<0.0 then begin
   	     z[2] := z[1]; z[1] := 0.0;
      end;

      if ind=2 then begin
         f[1] := y[3]; f[2] := y[4];

         cqrt;

         z[3] := g[1]; z[4] :=  g[2];
         z[5] := z[3]; z[6] := -z[4];
      end;

      if (ind=4) or (ind=0) then begin
         z[3] := sqrt(abs(y[3]));
      	 z[4] := 0.0;

         if y[3]<0.0 then begin
            z[4] := z[3];
	          z[3] := 0.0;
	       end;

         z[5] := sqrt(abs(y[5]));
	       z[6] := 0.0;

         if y[5]<0.0 then begin
	          z[6] := z[3];
            z[5] := 0.0;
	       end;
      end;

      h[1] := 1.0;
      h[2] := 0.0;

      for i:=1 to 3 do begin
         j := 2*i - 1;
         g[1] := z[j];
         g[2] := z[j+1];
         f[1] := h[1]*g[1] - h[2]*g[2];
         f[2] := h[1]*g[2] + h[2]*g[1];
         h[1] := f[1];
         h[2] := f[2];
      end;

      if (h[1]*q)>0.0 then begin
         z[1] := -z[1];
         z[2] := -z[2];
      end;

      for i:=1 to 4 do
         for j:=1 to 2 do begin
            k := 2*(i - 1) + j;
            x[k] := ( w[i,1]*z[j] + w[i,2]*z[j+2] + w[i,3]*z[j+4] ) /2.0;
         end;

      dd := b /a /4.0;

      for i:=1 to 4 do begin
         k := 2*i - 1;
         x[k] := x[k] - dd;
      end;
   end;

   if ind=4 then for i:=1 to 4 do XRe[i] := X[2*i-1];

   if ind=2 then begin
      l := 1;

      for i := 1 to 3 do begin
         k := 0;

         for j := i + 1 to 4 do begin
            ss := x[2*i]*x[2*j];

            if (ss<0.0) and (abs(ss)>1.0e-40) then begin
               for k := 1 to 4 do
                  if (k<>i) and (k<>j) then XRe[l] := X[2*k-1];

               l := l + 1;

               goto 1;
            end;
         end;
      end;
   end;

   1:

   for k := 1 to ind do begin
      f0 := 1.0;
      i  := 1;
      xx := XRe[k];
	    f[1] := 1.0;
      f[2] := 0.0;

      while (abs(f0)>1.0e-1) and (abs(f[1]-f[2])>1.0e-10) do begin
          f1 := a*sqr(xx)*xx;
          f2 := b*sqr(xx);
          f3 := c*xx;
          f0 := (f1 + f2 + f3 + d)*xx + e;
          pr := 4.0*f1 + 3.0*f2 + 2.0*f3 + d;

          if abs(pr) < 1.0e-10 then begin
     //        MessageDlg('KVADRA: производная равна нулю', mtInformation,[mbOk], 0);
             goto 2;
          end;

          f[2] := f[1];
          dx   := f0/pr;
          f[1] := dx;
          xx   := xx - dx;

          if i>100 then begin
      //       MessageDlg('KVADRA: зацикливание при уточнении значения корня xRe['+inttostr(k)+')', mtInformation,[mbOk], 0);
             goto 2;
          end;

          i := i + 1;
      end;

      2:

      XRe[k] := xx;
   end;

END; (*Конец процедуры KVADRA *)

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

PROCEDURE KOEFF(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k,
                sin_D, cos_D, cos_A1, cos_A2: float;
                out F_u, F_k, a, b, c, d, e, f, Vr_u{m/c}, Vr_k, Vn_u, Vn_k: float); overload;
var Q_u, Q_k: float;
  // Расчет коэффициентов уравнения 4-й степени
BEGIN
   F_u := b00 /modR_u;
   F_k := b00 /modR_k;
   Q_u := SQRT(Fpar_u*1.0E3/b00);
   Q_k := SQRT(Fpar_k*1.0E3/b00);

   a   := 2.0*(sqr(F_u) + sqr(F_k) - 2.0*F_u*F_k*cos_D);
   d   := Exsc_u * SIN(degtorad(Anom_u)) /Q_u;
   Vr_u := d;
   e   := Exsc_k * SIN(degtorad(Anom_k)) /Q_k;
   Vr_k := e;

   b   := ( -d*( F_u*cos_D - F_k ) - Q_u*sqr(F_u)*cos_A1*sin_D +
          e*( F_k*cos_D - F_u ) - Q_k*sqr(F_k)*cos_A2*sin_D ) *sin_D;
   c   := 0.0;
   d   := d - e;
   e   := 1.0 - cos_D;
   f   := e;
   d   := d*e*sin_D;
   e   := -2.0*sqr(e);

   Vn_u := b00*Q_u /modR_u;
   Vn_k := b00*Q_k /modR_k;
END; // Конец процедуры KOEFF *)

PROCEDURE KOEFF(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k: float;
                out Vr_u{m/c}, Vr_k, Vn_u, Vn_k: float); overload;
var F_u, F_k, Q_u, Q_k: float;
  // Расчет коэффициентов уравнения 4-й степени
BEGIN
   F_u := b00 /modR_u;
   F_k := b00 /modR_k;
   Q_u := SQRT(Fpar_u*1.0E3/b00);
   Q_k := SQRT(Fpar_k*1.0E3/b00);

   Vr_u := Exsc_u * SIN(degtorad(Anom_u)) /Q_u;
   Vr_k := Exsc_k * SIN(degtorad(Anom_k)) /Q_k;

   Vn_u := b00*Q_u /modR_u;
   Vn_k := b00*Q_k /modR_k;
END; // Конец процедуры KOEFF *)

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

PROCEDURE VZLET(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k: float;
            out DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a: float);
VAR g: float;
    Vr_u{m/c}, Vr_k, Vn_u, Vn_k: float;
BEGIN //  Расчет вертикального взлета   {WRITELN('Почти вертикальный взлет');}

   KOEFF(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k,

          Vr_u{m/c}, Vr_k, Vn_u, Vn_k);

   g := (modR_u + modR_k) /2.0;
   g := b00 /sqr(g);

   IF modR_u<modR_k THEN BEGIN
      DVr_u := sqrt( 2.0*g*(modR_k - modR_u) ) - Vr_u;
      DVr_k := Vr_k
   END
   ELSE BEGIN
      DVr_k := Vr_k - SQRT(2.0*g*(modR_u - modR_k) );
      DVr_u := -Vr_u
   END;

   DVn_u := -Vn_u;
   DVn_k :=  Vn_k;
   DVb_u := 0.0;
   DVb_k := 0.0;

   DV_u := SQRT( sqr(DVr_u) + sqr(DVn_u) + sqr(DVb_u) );
   DV_k := SQRT( sqr(DVr_k) + sqr(DVn_k) + sqr(DVb_k) );
   a    := DV_u + DV_k;
END; //  Конец процедуры VZLET *)

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

PROCEDURE IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
                 F_u, F_k, Vn_u, Vn_k, Vr_k: float;

             out a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k: float);
BEGIN
   // Расчет суммарного импульса потребной скорости    a
   //g=SQRT(Fpar_переходной/mju)    f=1.0-COS_D
   if g<>0 then begin
   a     := f/g;

   DVr_u := -Vr_u;

   IF ABS(sin_D) > 1.0E-5 THEN
      DVr_u := DVr_u + (g* (F_u*cos_D - F_k) + a) /sin_D;

   DVn_u := g*F_u*cos_A1 - Vn_u;
   DVb_u := g*F_u*sin_A1;
   DVr_k := Vr_k;

   IF ABS(sin_D) > 1.0E-5 THEN
      DVr_k := DVr_k + (g* (F_k*cos_D - F_u) + a) /sin_D;

   DVn_k := Vn_k - g*F_k*cos_A2;
   DVb_k := {-}g*F_k*sin_A2;                    {!!!!!!!!!!!!!}
   DV_u  := SQRT( sqr(DVr_u) + sqr(DVn_u) + sqr(DVb_u) );
   DV_k  := SQRT( sqr(DVr_k) + sqr(DVn_k) + sqr(DVb_k) );
   a     := DV_u + DV_k;
   end
   else begin
     a:=1e999; DVr_u:=1e999; DVn_u:=1e999; DVb_u:=1e999; DVb_k:=1e999;
     DVr_k:=1e999; DVn_k:=1e999; DV_u:=1e999; DV_k:=1e999;
   end;
END; // Конец процедуры IMPULS *)

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

PROCEDURE POLUOS(q, cos_D, sin_D, modR_u, modR_k: float; out  Bpol: float);
  // Расчет большой полуоси орбиты перелета
  //       q = SQRT(Fpar_перех./mju)
VAR a, b, c, d, Fpar: float;
BEGIN
   Fpar := sqr(q) * b00;

   IF ABS(sin_D)<1.0E-5 THEN Bpol := (modR_u + modR_k)/2.0
   ELSE BEGIN
      d := modR_u /modR_k;
      a := sqr(sin_D);
      b := (Fpar/modR_u)-1.0;
      c := d - 1.0;
      Bpol := Fpar*a /( a - (sqr(d) - 2.0*d*cos_D + 1.0) *sqr(b) + 2.0*c*b*(cos_D - d) - sqr(c) );
   END
END; //(* Конец процедуры POLUOS *)

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
PROCEDURE FOKPAR(cos_D, sin_D, modR_u, modR_k, Bpol: float; out q1, q2: float);
//     Расчет значений  q1 ,  q2  по большой полуоси  Bpol

VAR a, b, c, d, e, Fpar: float;
BEGIN
   d := modR_u/modR_k;
   e := sqr(sin_D);
   c := d - 1.0;
   a := sqr(d) - 2.0*d*cos_D + 1.0;
   b := modR_u*e/Bpol - 2.0*c*(cos_D - d);
   c := (modR_u/Bpol - 1.0)*e + sqr(c);
    (* Проверка дискриминанта *)
   IF (sqr(b)-4.0*a*c) < 0.0 THEN d := 0.0
                             ELSE d := SQRT( sqr(b) - 4.0*a*c);

   q1 := ( (d-b) /2.0 /a + 1.0 )   *modR_u;
   q2 := ( 1.0 - (b + d) /2.0 /a ) *modR_u;

   { проверка соответствия второго значения
   c:=modR_u*modR_u*SQR(1.0-cos_D)/a/Fpar;
   WRITELN(q1:15:3,'  ',q2:15:3,'  ',c:15:3); }

   IF q1<0.0 THEN BEGIN
      IF q2<0.0 THEN BEGIN
     	   q1 := 0.0;
         q2 := 0.0
      END ELSE
       	 q1 := q2
   END
   ELSE IF q2<0.0 THEN q2 := q1;

   q1 := SQRT(q1/b00);
   q2 := SQRT(q2/b00);
END; (* Конец процедуры FOKPAR *)

//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
procedure DVminQ( r0, r1, fi, v0, Q0, PSI:float;
                  var V, Q, DVmin, ALFA, BETTA:float;
                  var neudacha:integer);
      (*===============================================================¬
      ¦Процедура вычисляет  минимальный импульс скорости          ¦
      ¦                                                                ¦
      ¦   ВХОДНЫЕ ПЕРЕМЕННЫЕ:                                 ¦
      ¦              r0 - радиус начальной точки                       ¦
      ¦              r1 - радиус конечной точки                        ¦
      ¦              fi - угловая дальность перелета                   ¦
      ¦              V0 - начальная скорость                           ¦
      ¦              Q0 - угол наклона скорости                        ¦
      ¦              PSI - угол разворота плоскости орбиты при  PSI>0 - разво-  ¦
      ¦                 роте плоскости влево            ¦
      ¦                                                                ¦
      ¦   ВЫХОДНЫЕ ПЕРЕМЕННЫЕ:                                ¦
      ¦              V, Q - требуемая скорость и угол наклона,         ¦
      ¦                     обеспечивающие минимальный импульс         ¦
      ¦              DVmin - минимальный импульс                       ¦
      ¦                                                                ¦
      ¦              ALFA, BETTA - углы ориентации минимального        ¦
      ¦                 импульса:   ALFA отсчитывается                 ¦
      ¦                 от вектора Vt0 в плоскости                     ¦
      ¦                 исходной орбиты, 0<=ALFA<360,                  ¦
      ¦                 BETTA - от плоскости орбиты до вектора DVmin,  ¦
      ¦                 -90<=BETTA<=+90 (BETTA>0  при  PSI>0 - разво-  ¦
      ¦                 роте плоскости влево;
                                ¦
      ¦              neudacha - индикатор :                            ¦
      ¦                0 - благополучное  завершение                   ¦
      ¦                1 - неудачные исходные данные: fi=0 или fi=360  ¦
      ¦                2 - ошибочный расчет коэффициентов уравнения,   ¦
      ¦                    вследствие чего получилось 4 вещественных   ¦
      ¦                    корня, а этого не может быть                ¦

      ¦            ГЛОБАЛЬНЫЕ ДАННЫЕ И КОНСТАНТЫ                       ¦
      ¦            b00 - постоянная гравитационного поля Земли         ¦
      ¦                                                                ¦
      ¦            ВНЕШНИЕ ПРОЦЕДУРЫ И ФУНКЦИИ                         ¦

      ¦             KVADRA, KUB                                        ¦
      ¦                                                                ¦
      L===============================================================*)
const eps=1.0e-5;
var a, b, c, d, e, aa, bb, t, tg, vt, vr, vt0, vr0, vv, xx, yy,
    cp, sp, sQ, coQ, st, Qa, va, vb, dv, s, Vh, f1, f2, f3, pr,
    dx, ss, Qb, sa, ca, p, sf, cf, f, co, si, u, w, x0, y0:  float;

    ind, i, j, k: integer;
    ddv, cq, vtr, ttg: array[1..4] of float;
    x, y, XRe: v10;

begin
  if abs(sin(fi/2))<1e-16 then begin
//     writeln(' DVminQ:   Угловая дальность перелета равна 0. ', ' Нажмите ВВОД');
     neudacha := 0; exit;
  end;

  neudacha := 1;
  sincos(psi, sp, cp);
  sincos(Q0, sQ, coQ);

  if abs(psi)<1e-7 then
  begin // плоский маневр
     Vb := V0;
     Vh := 0;
     Qb := Q0;
  end
  else begin // пространственный маневр
     if abs(cp)<1e-6 then
        if Q0>0 then Qb :=  pi/2
                else Qb := -pi/2
     else Qb := arctan( sq /coQ /cp);

     Vb := V0*coQ *sqrt( sqr(cp) + sqr(sQ/coQ) );
     Vh := sqrt( sqr(V0) - sqr(Vb) );
  end;

  vt0 := Vb*cos(Qb); vr0 := Vb*sin(Qb);

  if abs(pi-fi)<1.0e-9 then begin
     vr := vr0;
     vt := sqrt( b00/r0 * 2.0 /(r0/r1 + 1.0) );

     Q  := arctan(vr / vt);
     ca := vt - vt0;
     V  := sqrt( sqr(Vt) + sqr(vr) );

     DVmin := abs(ca);

  end else
  begin

     sincos(fi/2.0, sf, cf);
     u := 2.0 *b00 * sqr(sf) /r0;
     p := r0/r1 + sqr(sf) - sqr(cf);

     if abs(p)<1e-12 then f := pi/2
     else begin
        tg := 2.0*abs(sf*cf)/p;
        f  := arctan(tg);
        if f < 0.0 then f := f + pi;
     end;

     sincos(f/2.0,  si, co);
     if fi>pi then si := -si;

     w  := 2.0 * si*co *sf*cf;
     x0 :=  vt0*co + vr0*si;
     y0 := -vt0*si + vr0*co;
     aa := abs( u / (co*co*p + w));
     bb := abs(-u / (si*si*p - w));

     a  := aa + bb;

     b  := -2.0*aa /a*x0;

     c  := aa /sqr(a) *( aa*sqr(x0) - bb*sqr(y0) - sqr(a));

     d  := 2.0 * sqr(aa) /a *x0 ;

     e  := -aa / sqr(a) *sqr(aa) *sqr(x0);

     a:=1.0;
//     KVADRA2(a, b, c, d, e, Xre, ind);  //??????????????????????????????????????
{writeln(' KVADRA2: ind=',ind,' X1=',Xre[1]:4:3,' X2=',Xre[2]:4:3,' X3=',Xre[3]:4:3,' X4=',Xre[4]:4:3);}

     if ind <> 2 then
     begin
       KVADRA(a, b, c, d, e, ind, x, y, XRe);
       {writeln(' KVADRA : ind=',ind,' X1=',Xre[1]:4:3,' X2=',Xre[2]:4:3,' X3=',Xre[3]:4:3,' X4=',Xre[4]:4:3);  }
     end;

     k:=0;

     if ind>0 then

       for j:=1 to ind do begin
         xx := XRe[j]; // XRe[j] - необъявлена ++++++++!!!!!!!!!!!!!!!!!!!!!!!!!!!!
         ss := sqrt(aa);

         if (abs(xx)-ss)>-1.0e-4 then begin
            inc(k);
            yy := sqrt( bb * abs(xx*xx - aa) /aa );
            if abs(y0 + yy) < abs(y0 - yy) then yy := -yy;
            vt := xx*co - yy*si;
            vr := xx*si + yy*co;
            ttg[k] := vr/vt; tg := ttg[k];
            vv := sqrt( sqr(vr) + sqr(vt) );

            vtr[k] := vv;
             cq[k] := vt / vv;
            ddv[k] := sqrt( sqr(vt-vt0) + sqr(vr-vr0) );
            if vt<0.0 then ddv[k] := ddv[k]*1.0e6;
         end;
       end;

     if k<>2 then begin
         MessageDlg('DVminQ: кол-во корней не равно 2: k= '+inttostr(k), mtInformation,[mbOk], 0);
         neudacha:=2;
         exit;
     end;

     if ddv[1]<ddv[2] then k:=1
                      else k:=2;

     V:=vtr[k]; Q:=arctan(ttg[k]);
     DVmin:=ddv[k];
  end; {  fi<>pi  }

  sincos(Q, sQ, coQ);
  DVmin := sqrt( sqr(dvmin) + sqr(Vh) );
  if abs (cp)>eps then Qa := arctan(sQ/coQ/cp)
                  else Qa := 0.0;
  Va := V *sqrt( 1.0 - sqr(sp)*sqr(coQ) );
  Vr := V*sQ;
  Vt := V*coQ;
  a  :=(Vr-vr0)/DVmin;
  b  :=(Vt-vt0)/DVmin;

  ALFA  := arctan2(a,b); // PTAN()
  dv    := sqrt(sqr(v0) + sqr(va) - 2.0*v0*va*cos(Q0-Qa));
  BETTA := arctan( V*coQ * sp/dv);
end; {  DVminQ  }



//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------

function GoldSRea(a, b, epsF, epsX: real; f:func1):real; //f:func1???????????????????????????????????????????
label 20;

Const
   lmbd = 0.6180339887;

var fx, fx1, fx2, x, x1, x2: real;
    j: integer;

BEGIN
   x1 := a;
   x2 := b;
   fx1 := f(x1);
   fx2 := f(x2);

   if abs(fx1)<epsF then GoldSrea := x1 else
   if abs(fx2)<epsF then GoldSrea := x2 else

   if (fx1*fx2)<0.0 then begin
      j:=0;

      while (abs(x2-x1))>epsX do begin
         x := x1 + lmbd*(x2 - x1);
         fx := f(x);
         inc(j);
         {writeln(' ***  цикл  ***        j=',j);                        }
         if j>100 then MessageDlg('Зацикливание в процедуре GoldSrea, число итераций >100', mtInformation,[mbOk], 0);

         if abs(fx) < epsF then begin
      	   GoldSrea:=x;
     	     goto 20;
 	       end;

         if (fx1*fx)<0.0 then begin
 	         x2  :=  x;
	         fx2 := fx;
	       end else
         if (fx2*fx)<0.0 then	begin
     	     x1  :=  x;
	         fx1 := fx;
 	       end;

      end;

      GoldSrea:=x;

   end
   else MessageDlg('В процедуре-функции GoldSrea f(x1)*f(x2)>0', mtInformation,[mbOk], 0);
20:
END;


//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
(*
{======================================================================}
procedure Optimizacia_bak(N_KA, m, n : byte; dOm1, dOm2, dOm_m1, dOm_m2 : real);
var
    i, j, k1, k2, k3, l1, l2, l3, nm, jj            : byte;
    du, du_m, dOm, dOm_m, dlt_Om, dlt_u, d, dlt_um,
    dlt_Om_m, dlt_u_m, B1D, gm, Fiz0, Fiz, dum      : real;

begin
   /Naklonenie:=11;///__________________!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! zadat glob perem
   nm := N_KA - (m-1)*n;
   du := 2*pi/n;
   du_m := 2*pi/nm;
   k1 := 5;
   k2 := 5;
   k3 := 5;
   dlt_Om := (dOm2 - dOm1)/(k1 -1);

   for l1:=1 to k1 do begin

      dOm   := dOm1 + dlt_Om*(l1 - 1);
      B1D   := arctan( cos(Naklonenie) *sin(dOm/2) / cos(dOm/2) );
      gm    := arcsin( sin(Naklonenie) *sin(dOm/2) );
      Fiz0  := arccos( cos(gm) *cos(du/2) );
      dOm_2 := (m-1)*dOm - pi;
      gm2   := arccos( cos( dOm_2/2 ) * sin(Naklonenie));
      //writeln(' dOm= ',dOm*gra:9:3,'  Fiz0= ',Fiz0*gra:9:3,
      //  ' gm1=',gm*2*gra:9:2, ' gm2=',gm2*2*gra:9:2);
      {readln;}
      dlt_u    := -2*B1D + du/2;

      if nm=n then begin
         k2 := 1;
         dlt_Om_m := 0;
      end
      else dlt_Om_m := (dOm_m2 - dOm_m1) /(k2 - 1);

      for l2 := 1 to k2 do begin
         dOm_m := dOm_m1 + (l2 - 1) * dlt_Om_m;

         if nm = n then begin
            k3 := 1;
            dum := dlt_u;
         end
         else dum := (dlt_u - du) /( k3 - 1);

         for l3 := 1 to k3 do begin
            du_m := dlt_u + dum*(l3-1);

            for i:=1 to n*(m-1) do begin
               j := 1 + ROUND(i/n - 0.51);
               Om_KA[i]:=(j-1)*dOm ;
               u0_KA[i]:=(j-1)*dlt_u + du*(i - n*(j-1) - 1);
            end;

            for i:=1 + n*(m-1) to N_KA do begin
               Om_KA[i]:=(m-2)*dOm + dOm_m;
               u0_KA[i]:=(m-1)*dlt_u + du_m*(i - n*(m-1) - 1);
            end;

            for jj:=1 to N_KA do
               //writeln(' jj=',jj:3,' Om=',gra*Om_KA[jj]:9:3,' u0=',gra*u0_KA[jj]:9:3);
               Analiz_All_Gran;
               Uzkoe_mesto( du_R_okr_max, R_okr_max, k_KA_mal, KA_mal );
               R_okr_max:=90 - arccos(R_okr_max)*gra;
               //writeln(' dOm=',dOm*gra:5:1,' dOm_m=',dOm_m*gra:5:1,' dum=',dum*gra:5:1,
               // ' Fiz0= ',Fiz0*gra:9:3,'  R_okr_max= ',R_okr_max:9:3);
            end;
         end;
      end;
end;

{======================================================================}
{======================================================================}
{======================================================================}
{======================================================================}

{N<>n*m}
procedure Optimizacia_2(N_KA, m, n : byte; Fiz, u0_m : real);

var i, j, k1, k2, k3, l1, l2, l3, nm, jj: byte;
    du, du_m, dOm, dOm_m, dlt_Om, dlt_u, d,
    dlt_um, a, b, am, bm,
    dlt_Om_m, dlt_u_m, B1D, gm, Fiz0,  dum      : real;

begin
   nm := N_KA - (m-1)*n;
   du := 2*pi/n;
   du_m := 2*pi/nm;
   a  := pi/n;
   b  := arccos(cos(Fiz)/cos(a));
   dOm := arccos((cos(b+Fiz) - sqr(cos(Naklonenie)))/sqr(sin(Naklonenie)));
   am  := pi/nm;
   bm  := arccos(cos(Fiz)/cos(am));
   dOm_m := arccos((cos(b+bm) - sqr(cos(Naklonenie)))/sqr(sin(Naklonenie)));
   dlt_Om := 2*pi - (m-2)*dOm - dOm_m;
   gm2 := 2*arccos(cos(dlt_Om/2)*sin(Naklonenie));

   if gm2>pi then gm2 := gm2 - pi;

   //if gm2 > b + bm then
   //writeln(' Fiz=',Fiz*gra:4:2,' ПЛОХО :  gm2 > b + bm: gm2=',gm2*gra:9:5,' b + bm=',(b + bm)*gra:9:5)
   //else
   //writeln(' Fiz=',Fiz*gra:4:2,' ХОРОШО:  gm2 < b + bm: gm2=',gm2*gra:9:5,' b + bm=',(b + bm)*gra:9:5);

   gm    := 2*arcsin(sin(Naklonenie)*sin(dOm/2));
   B1D   := arccos(cos(dOm/2)/cos(gm/2));
   dlt_u := -2*B1D + du/2;

   if nm = n then u0_m := dlt_u *(m - 1);

   for i := 1 to n*(m-1) do  begin
      j := 1 + ROUND(i/n - 0.51);
      Om_KA[i] := (j-1)*dOm + eps*(Random - 0.5); //????????????????????????????????????????????????
      u0_KA[i] := (j-1)*dlt_u + du*(i - n*(j-1) - 1) + eps*(Random - 0.5);
   end;

   for i:=1 + n*(m-1) to N_KA do begin
      Om_KA[i] := (m-2)*dOm + dOm_m + eps*(Random - 0.5);      //???????????????????????????????????
      u0_KA[i] := u0_m + du_m*(i - n*(m-1) - 1) + eps*(Random - 0.5);
   end;

   {for jj:=1 to N_KA do
   writeln(' jj=',jj:3,' Om=',gra*Om_KA[jj]:9:3,' u0=',gra*u0_KA[jj]:9:3);
   }
   //readln;
   halt; //??????????????????????????????????

   Dinamika_Grani(1, 2, 5, 0*rad, 0.5*rad, dmin, uzmin);

   Analiz_All_Gran;

   Uzkoe_mesto( du_R_okr_max, R_okr_max, k_KA_mal, KA_mal );

   R_okr_max := 90 - arccos(R_okr_max)*gra;
   writeln('  R_okr_max= ',R_okr_max:9:3);
   report; //????????????????????????????/
end;
*)


{======================================================================}
{======================================================================}
{======================================================================}
{======================================================================}
(*
{$F+}
function f0(x:real):real;
var b : real;
begin
  b:=(pi - (m-1)*x)/(m+1);
  f0:=cos(x) - cos(pi/n)*cos(b);
writeln((cos(x) - cos(pi/n)*cos(b)):9:4,'  fz=',x*180/pi:9:3,'  b=',b*180/pi:9:3);
end;
{$F-}
*)

{======================================================================}
{======================================================================}
{======================================================================}
{======================================================================}
(*
{N=n*m}
procedure Optimizacia(N_KA, m, n : byte; Fiz, u0_m : real);
var i, j, k1, k2, k3, l1, l2, l3, nm, jj            : byte;
    du, du_m, dOm, dOm_m, dlt_Om, dlt_u, d, dlt_um,
    a, b, am, bm,
    dlt_Om_m, dlt_u_m, B1D, gm, Fiz0,  dum      : real;
begin
  du     := 2*pi/n;
  a:=pi/n;
  b:=arccos(cos(Fiz)/cos(a));
  dOm:=arccos((cos(b+Fiz) - sqr(cos(Naklonenie)))/sqr(sin(Naklonenie)));
  dOm_m:=pi - (m - 1)*dOm;
  if dOm_m<0 then
  begin
writeln('dOm_m<0');
readln;
    dOm:=pi/(m - 1);
    dOm_m:=0;
  end;

  gm2:=2*arccos(cos(dOm_m/2)*sin(Naklonenie));
  if gm2>pi then
    gm2:=gm2 - pi;
if gm2 > 2*b then
writeln(' Fiz=',Fiz*gra:4:2,' ПЛОХО :  gm2 > 2*b: gm2=',gm2*gra:9:5,' b + bm=',2*b*gra:9:5,
        ' dOm=',dOm_m*gra:4:2)
else
writeln(' Fiz=',Fiz*gra:4:2,' ХОРОШО:  gm2 < 2*b: gm2=',gm2*gra:9:5,' b + bm=',2*b*gra:9:5,
        ' dOm=',dOm_m*gra:4:2);

  gm       := 2*arcsin(sin(Naklonenie)*sin(dOm/2));
  B1D      := arccos(cos(dOm/2)/cos(gm/2));
  dlt_u    := -2*B1D + du/2;

  u0_m     := dlt_u*(m-1);
  du_m     := du;

  for i:=1 to n*m do
  begin
    j:=1 + ROUND(i/n - 0.51);
    Om_KA[i]:=(j-1)*dOm + eps*(Random - 0.5);
    u0_KA[i]:=(j-1)*dlt_u + du*(i - n*(j-1) - 1) + eps*(Random - 0.5);
  end;
{  for i:=1 + n*(m-1) to N_KA do
  begin
    Om_KA[i]:=(m-2)*dOm + dOm_m + eps*(Random - 0.5);
    u0_KA[i]:=u0_m + du_m*(i - n*(m-1) - 1) + eps*(Random - 0.5);
  end;}
for jj:=1 to N_KA do
writeln(' jj=',jj:3,' Om=',gra*Om_KA[jj]:9:3,' u0=',gra*u0_KA[jj]:9:3);

  STR(N_KA,st);
  SaveParOrbit('ParOrbit.'+st);

readln;
halt;
for jj:=1 to N_KA do
writeln(' jj=',jj:3,' Om=',gra*Om_KA[jj]:9:3,' u0=',gra*u0_KA[jj]:9:3);
Dinamika_Grani(1,2,5,0*rad,0.5*rad, dmin, uzmin);

  Analiz_All_Gran;
  Uzkoe_mesto( du_R_okr_max, R_okr_max, k_KA_mal, KA_mal );
  R_okr_max:=90 - arccos(R_okr_max)*gra;
  writeln('  R_okr_max= ',R_okr_max:9:3);
  report;
end;
{======================================================================}
*)




{**************************************************************************}
{*                                                                        *}
{*                   Б И Б Л И О Т Е К А                                  *}
{*                                                                        *}
{*                   С Т А Н Д А Р Т Н Ы Х                                *}
{*                                                                        *}
{*                   Ф У Н К Ц И Й    И                                   *}
{*                                                                        *}
{*                   П Р О Ц Е Д У Р                                      *}
{*                                                                        *}
{**************************************************************************}


{-------------------------------------------------------------------------}

//============================================================
//============================================================
//============================================================
 {г==========================================================¬
  ¦     Расчет эксцентрической аномалии                      ¦
  L==========================================================-}

Function EEE(tt, exs: float): float;
// tt - истинная аномалия, рад
// exs - эксцентриситет
Var s, c, se, ce, a, al: float;
    k: integer;

Begin
   al := tt/2.0/pi;
   k  := trunc(al);
   al := tt - k*pi*2.0;

   if al<0.0 then begin
      al := al + 2.0*pi;
      dec(k);
   end;
   sincos(al, s, c);
   a  := 1.0 + exs*c;
   se := s*sqrt(1.0 - sqr(exs)) /a;
   ce := (exs + c)/a;
   a  := ptan(se, ce);
   eee:= a + 2.0*k*pi;
End;{ EEE }

//============================================================
//============================================================
//============================================================

Function HHH(tt, exs: float): float;
 {г==========================================================¬
  ¦     Расчет гиперболической  аномалии                     ¦
  L==========================================================-}
//
Var  s: float;
Begin
   s := sqrt( sqr(exs) - 1.0 ) *sin(tt) /(1.0 + exs*cos(tt));
   s := ln( s + sqrt( sqr(s) + 1.0) );
   hhh := s;
End; { HHH }

//============================================================
//============================================================
//============================================================

Function  TTT(p, ex, tt0, t0, t:float):float;
// p    фок параметр, м
// ex   эксцентр
// tt0  истинн аном на момент врем t0, сек
// t0   нач мом вр , сек
// t    кон мом врем , сек
 {г==========================================================¬
  ¦  Расчет положения объекта tt(ист. ан.) на текущий момент ¦
  ¦  t по начальному положению tt0 в момент t0               ¦
  L==========================================================-}
Const  lmbd = 0.6180339887;
       epst = 0.1e-4;
       epsx = 0.1e-8;
Var a,b,tt_gip,omi,oma,om,f,f1,f2,tt:float;
    k:integer;

Begin
   if ex<1.0e-8 then begin
      ttt := tt0 + (t - t0)*sqrt(b00/p/p/p);
      Exit;
   end;

   k   := 2;
   om  := sqrt(b00/p/p/p);
   oma := om*sqr(1.0 + ex);
   a   := tt0;
   b   := tt0 + oma*(t-t0);

   if (ex>0.999999) and (b>pi) then b := pi - 0.001;

   if (ex>1) then  begin
      tt_gip := arccos(-1/ex);

      if b>tt_gip then b := tt_gip - 0.001;

      if a>b then b := b + 2*pi;
   end;

   if ex<1.0 then begin
      omi := om*sqr(1.0-ex);
      a   := tt0 + omi*(t - t0);
   end;

   tt := a;
   f1 := t0 + TVSTR(tt0, tt, p, ex) - t;
   ttt:= tt;

   if abs(f1)<epst then Exit;

   tt := b;
   f2 := t0 + TVSTR(tt0, tt, p, ex) - t;
   ttt:= tt;

   if abs(f2)<epst then Exit;

   while (abs(b-a)>epsx) and (k<=202) do begin
      inc(k);
      tt := a + lmbd*(b - a);
      f  := t0 + TVSTR(tt0, tt, p, ex) - t;
      ttt:= tt;

      if abs(f)<epst then Exit;

      if f1*f<0.0 then begin
         b  := tt;
//         f2 := f;    //??????????????????????????????????????????????/ не используется
      end
      else begin
         a  := tt;
         f1 := f;
      end;
   end;
End{  TTT  };

//============================================================
//============================================================
//============================================================
 {г==========================================================¬
  ¦              Расчет времени  ВСТРЕЧИ                     ¦
  L==========================================================-}
Function TVSTR( tt0, tt1, p, exs: float): float;
Label 10;
Var t0,t1,a,e0,e1,h0,h1:float;

Begin
   if abs(exs - 1)<1.0e-9 then begin
      t0 := tan(tt0); //sin(tt0)/cos(tt0);
      t1 := tan(tt1); //sin(tt1)/cos(tt1);
      tvstr := sqrt(p*p*p/b00)*(t1 - t0 + (t1*t1*t1 - t0*t0*t0)/3.0);
      goto 10;
   end;
   if exs<1.0 then begin
      e0 := eee(tt0, exs);
      e1 := eee(tt1, exs);

      if e1<e0 then e1 := e1 + 2.0*pi;

      a := p/(1.0 - sqr(exs));
      tvstr := sqrt(a*a*a/b00) *(e1 - e0 - exs*(sin(e1) - sin(e0)));
      goto 10;
   end;

   h0 := hhh(tt0, exs);
   h1 := hhh(tt1, exs);
   a  := p/(sqr(exs) - 1.0);
   tvstr := -sqrt(a*a*a/b00) *(h1 - h0 - exs*(sinh(h1) - sinh(h0)));
   10:
End; {  TVSTR  }

//============================================================
//============================================================
//============================================================
 {г==========================================================¬
  ¦           Расчет  ИСТИННОЙ аномалии                      ¦
  L==========================================================-}

Function TETT( p, r, exs, Q: float): float;
Var tt,ct,st: float;

Begin
   tt := 0.0;

   if exs<1.0e-5 then tett := tt
   else begin
      ct := (p/r - 1.0)/exs;

      if abs(abs(ct)-1.0)<1.0e-6 then st := 0.0
                                 else st := sqrt(1.0 - sqr(ct));

      if sin(Q)<0.0 then st := -st;

      tt := ptan(st,ct);
      tett := tt;
   end;
End; { TETT }

//============================================================
//============================================================
//============================================================
{======================================================================}
  {  Pасчет начальных входных параметров для процедуры определения  модельных
             управлений по импульсной кеплеровской теории: DvminQ }

Procedure RVQpl(vxk, xye, wxzd, uvxk, ivye, oMvzd: float;
                Var R0, V0, Q0,
                    xkn, yen, zdn, vxkn, vyen, vzdn, {-нормализованные параметры R0,V0 }
                    A1, B1, C1, K1 : float); {Параметры пл. начального эллипса в норм. виде    }


VAR  xag, yag, zag,
     avx, avy, avz,
     vx, vy, vz, vtau, sal, cal, cfi,
     vgip, gipa, sf, cf, sl, cl, sq0, cq0 :float;
     {.................................................................}
BEGIN
   xag := vxk; yag := xye; zag := wxzd;

   R0  := SQRT( sqr(vxk) + sqr(xye) + sqr(wxzd) );
   V0  := SQRT( sqr(uvxk) + sqr(ivye) + sqr(oMvzd) );

   gipa := SQRT( sqr(yag) + sqr(zag) );
   sf   :=  vxk/R0;
   cf   := gipa/R0;
   sl   := wxzd/gipa;
   cl   :=  xye/gipa;

   vx :=  uvxk*cf - ivye*sf*cl - oMvzd*sf*sl;
   vy :=  uvxk*sf + ivye*cf*cl + oMvzd*cf*sl;
   vz :=          - ivye*sl    + oMvzd*cl;

   vgip := sqrt( sqr(vx) + sqr(vz));
   sq0 := vy/V0;
   cq0 := vgip/V0;

   if (sq0>1.0)  then sq0 :=  1.0;
   if (sq0<-1.0) then sq0 := -1.0;
   if (cq0>1.0)  then cq0 :=  1.0;
   if (cq0<-1.0) then cq0 := -1.0;

   Q0 := PTAN(sq0, cq0);

   {нормировка параметров}
   xkn := xag/r0; yen := yag/r0; zdn := zag/r0;

   { Oпр. коэ-в уравнения плоскости начального эллипса - V0#R0}
   vxkn := uvxk/V0; vyen := ivye/V0;   vzdn := oMvzd/V0;

   a1   := -yen*vzdn + vyen*zdn;
   b1   :=  xkn*vzdn - vxkn*zdn;
   c1   := -xkn*vyen + vxkn*yen;

   { Расчет направляющих COS перпендикуляра к плоскости начального эллипса A1x+B1y+C1z=0}
   k1   := sqrt( sqr(A1) + sqr(B1) + sqr(C1) );

   if k1>1.0 then k1 := 1.0;

   A1 := A1/k1; B1 := B1/k1; C1 := C1/k1;

   if ABS(A1)<1.0e-19 then a1 := 0.0;
   if abs(B1)<1.0e-19 then b1 := 0.0;
   if abs(C1)<1.0e-19 then c1 := 0.0;
END;
 {=========================================================================}

//============================================================
//============================================================
//============================================================
 {г==========================================================¬
  ¦                                                          ¦
  ¦  Расчет входных параметров для процедуры определения     ¦
  ¦    времени перелета  и других случаев                    ¦
  ¦                                                          ¦
  L==========================================================-}

Procedure RVQ0(    pri : byte;
                   xi, yp, ze, Vxw, VyOmb, Vzu: float;
               Var R0, V0, Q0:float);

      {  НАЧАЛЬНЫЕ параметры движения в точке расчета управлений:
                      pri  ¦ 0      1
                      -----¦---------
                       xi  ¦  i     x
                       yp  ¦  p     y
                       ze  ¦  e     z
                       Vxw ¦  w     Vx
                      Vyomb¦  oMb   Vy
                       Vzu ¦  u     Vz

         R0-НАЧАЛЬНЫЕ расстояние
         V0-          скорость
         Q0-          угол накл. вектора V0 к пл. МГ                     }

VAR teta, ut, vrc, vpc, Ct, sq0, cq0 :float;
     {.................................................................}
Begin
   CASE pri of
   1: begin
        R0  := SQRT( sqr(xi) + sqr(yp) + sqr(ze) );
        V0  := SQRT( sqr(Vxw) + sqr(VyOmb) + sqr(Vzu));
        sq0 := (xi*Vxw + yp*VyOmb + ze*Vzu)/R0/V0;

        if (sq0>1.0)  then sq0 :=  1.0;
        if (sq0<-1.0) then sq0 := -1.0;
        cq0 := sqrt( 1 - sqr(sq0) );
        if (cq0>1.0) then cq0 := 1.0;
        Q0 := PTAN(sq0, cq0);
      end;

   0: begin
        if ze>0.1e-8 then begin
           teta := Vzu - Vxw;
           if teta<0.0 then  teta := teta + 2*pi;

           Ct := COS(teta);
           R0 := yp/(1 + ze*Ct);
           ut := sqrt(b00/yp);
           vrc:= ut*ze*sin(teta);
           vpc:= ut*(1.0 + ze*Ct);
           V0 := SQRT( sqr(vrc) + sqr(vpc) );
           Q0 := ArcTan( ze*SIN(teta)/(1 + ze*Ct));
        end
        else begin
           R0 := yp;
           Q0 := 0.0;
           V0 := sqrt(B00/yp);
        end;
      end;
   end { Case };
End;

//============================================================
//============================================================
//============================================================
 {г==========================================================¬
  ¦              Расчет ВРЕМЕНИ перелета                     ¦
  L==========================================================-}

Function Tper(v0, q0, r0, fi: float): float;
Var nu, c, {w,} p, exs, tt0, tt1:float;

Begin
   c := cos(q0);
   if c<>0.0 then c := sqr(c);

   nu  := sqr(V0)/(2.0*b00/r0);
   exs := sqrt( 1.0 - (1.0 - nu)*4.0*nu*c);

   if exs<1.0e-10 then tper := r0*fi/v0
   else begin
      p   := 2.0*r0*nu*c;
      tt0 := tett(p, r0, exs, Q0);
      tt1 := tt0 + fi;
      tper:= tvstr(tt0, tt1, p, exs);
   end;
End;

//============================================================
//============================================================
//============================================================
 {г==========================================================¬
  ¦     Расчет СКОРОСТИ и ВРЕМЕНИ перелета                   ¦
  L==========================================================-}
Procedure TAU(q0, r0, r1, fi: float; var DT, V0: float);
Var tg, cc, w, p, exs, tt0, tt1: float;

Begin
   cc := cos(q0);
   cc := sqr(cc);
   tg := sin(Q0)/cos(Q0);
   w  := (2.0*sqr(sin(fi/2.0)) *(1.0 + sqr(tg))) /(r0/r1 - cos(fi) + tg*sin(fi));
   v0 := sqrt(b00/r0*w);
   exs:= sqrt(1.0 - (2.0 - w)*w*cc);

   if exs<1.0e-5 then dt := r0*fi/v0
   else begin
      p   := w*r0*cc;
      tt0 := tett(p, r0, exs, Q0);
      tt1 := tt0 + fi;
      dt  := tvstr(tt0, tt1, p, exs);
   end;
End; {  TAU  }

//============================================================
//============================================================
//============================================================
 {г==========================================================¬
  ¦     Расчет параметров эллиптического движения            ¦
  L==========================================================-}
Procedure KEP( xk, ye, zd, vxk, vye, vzd: float;
              var i, p, e, w, te0, u0, ci, si, soMb, coMb, somm, comm,
                  ste0, cte0, su0, cu0: float);

Var C, Cx, Cy, Cz, F, Fx, Fy, Fz, r, v, mnr, csi, cfip,
    fi, sf, ut, la, omb: float;

Begin
   r := sqrt( sqr(xk) + sqr(ye) + sqr(zd) );
   v := sqrt( sqr(vxk) + sqr(vye) + sqr(vzd));
   mnr := -b00/r;
   {Постоянные площадей}
   Cy := zd*vxk - xk*vzd;
   Cz := xk*vye - ye*vxk;
   Cx := ye*vzd - zd*vye;
   C  := SQRT( sqr(Cx) + sqr(Cy) + sqr(Cz) );
   {Проекции вектора Лапласа на оси АГСК}
   Fy := mnr*ye + Cx*vzd - Cz*vxk;
   Fz := mnr*zd + Cy*vxk - Cx*vye;
   Fx := mnr*xk + Cz*vye - Cy*vzd;
   F  := SQRT(Fx*Fx + Fy*Fy + Fz*Fz);

   Ci := Cx/C;
   Si := SQRT(1.0 - Ci*Ci);
   i  := ptan(si, ci);

   if abs(i)<=1.0e-9 then i := 0.0;
   e := F/B00;

   if e<=1.0e-8 then e := 0.0;

   if e<=1.0e-8 then p := r
                else p := C*C/B00;

   if (i>0.0) and (i<pi) then begin
      csi  := C*si;
      somb := Cy/Csi;
      comb :=-Cz/Csi;
   end
   else begin
      somb := 0.0;
      comb := 1.0;
   end;

   omb := Ptan(somb, Comb);

   if (ABS(Omb-2*pi)<1.0e-9) or (ABS(Omb)<1.0e-9) then begin
      Omb  := 0.0;
      Somb := 0.0;
      Comb := 1.0;
   end;

   if e>=1.0e-8 then begin
      comm := (FZ*somb + FY*comb)/F;

      if (ABS(ci)>1.0e-9) then Somm := (Fz*comb - Fy*somb)/F/ci
                          else Somm := Fx/e/b00;

      w := ptan(somm, comm);

      if (ABS(ci)>1.0e-9) then begin
         cu0 := (zd*somb + ye*comb)/r;
         su0 := (zd*comb - ye*somb)/r/ci;
         u0  := Ptan(su0, cu0);
         te0 := u0 - w;
         if te0<0.0  then te0 := te0 + 2*pi;
         if te0>2*pi then te0 := te0 - 2*pi;

         sincos(te0, ste0, cte0) ;
      end
      else begin {расчет тета0 и U0 для полярной траектории}
         cte0 := (p/r - 1.0)/e;
         if cte0>=0.99999999999  then cte0 :=  0.999999999999999;
         if cte0<=-0.99999999999 then cte0 := -0.999999999999999;
         if ABS(cte0)>0.99999999998 then ste0 := 0.0
                                    else ste0 := SQRT(1.0e00 - cte0*cte0);
         cfip := xk*vxk + ye*vye + zd*vzd;

         if cfip<0.0 then ste0 := -ste0;
         te0 := ptan(ste0, cte0);
         u0  := te0 + w;

         if u0>=(2.0*pi) then u0 := u0 - 2.0*pi;
         if ABS(u0 - 2.0*pi)<0.1e-7 then u0 := 0.0;

         sincos(u0, su0, cu0);
      end
   end
   else{ if e<1.0e-8, т.е. для круговых орбит} begin
      somm := 0.0;
      comm := 0.0;
      w    := 0.0;

      sf   := xk/r;
      ut   := SQRT(ye*ye + zd*zd);
      la   := Ptan(zd/ut, ye/ut);

      if abs(i)>1.0e-9 then begin
         sf := sf/si;

         if sf>= 1.0 then sf :=  0.999999999999999;
         if sf<=-1.0 then sf := -0.999999999999999;
         cte0 := sqrt(1.0 - sf*sf) *sign( COS(la - omb) );

         if (abs(cte0)<1.0e-8) then cte0 := 0.0;
         ste0 := Sign(xk)*SQRT(1.0e00 - cte0*cte0);
      end
      else begin
         cte0 := ye/SQRT(ye*ye + zd*zd);
         ste0 := zd/SQRT(ye*ye + zd*zd);
      end;

      te0 := ptan(ste0, cte0);
      u0  := te0;
      su0 := Ste0;
      cu0 := Cte0;
   end{кругов. орбит.};

End;

//============================================================
//============================================================
//============================================================
{--------------------------------------------------------------------}
{  Программа изменения угла рыскания для поворота плоскости орбиты   }
{--------------------------------------------------------------------}
function Psi_t(psi_max, tn, tk, ti, t :float) :float;
var om, tau, a, b, c, d, p, p1, p2, pp : float;
    tau_i, tau_min, tau_max, Kr  : float;
begin
   tau_i := (ti - tn)/(tk - tn);
   tau_min := 1.5 - sqrt(2);
   tau_max := sqrt(2)-0.5;

   if tau_i < tau_min then tau_i := tau_min;
   if tau_i > tau_max then tau_i := tau_max;

   pp := 0.5;
   Kr := (3*sqrt(2)*(pp - tau_i))/(2*(pp + tau_i)*(pp + tau_i - 2));

   if (t>tk) or (t<tn) then begin
      psi_t := 0;
      exit;
   end;

   om := pi;
   tau := (t - tn)/(tk - tn);

   if abs(Kr)<1e-6 then p := tau
   else begin
      a := 2*Kr;
      b := 4*Kr*tau - 4*Kr - 3*sqrt(2);
      c := (3*sqrt(2) + 2*Kr*tau - 4*Kr)*tau;
      d := b*b - 4*a*c;
      if d<0 then d := 0
             else d := sqrt(d);
      p1 := (-b + d) /2/a;
      p2 := (-b - d) /2/a;
      p  := 0.5;
      if (p1<=1.00000001) and (p1>=-0.00000001) then p := p1;
      if (p2<=1.00000001) and (p2>=-0.00000001) then p := p2;
   end;
   Psi_t := psi_max * sqr(sin(om*p));
end; { Psi_t }

//============================================================
//============================================================
//============================================================
{---------------------------------------------------------------}
procedure Kep_Par(x, y, z, vx, vy, vz : float; var i, omb, p, e, omm, u : float);
const eps = 1e-10;
var   cx, cy, cz, c,  fx, fy, fz, f,  so, co, ci, d, v, r  : float;

begin
   r := Sqrt( x*x + y*y + z*z );
//   v := Sqrt( vx*vx + vy*vy + vz*vz);

   cx := y*vz - z*vy;
   cy := z*vx - x*vz;
   cz := x*vy - y*vx;
   c  := Sqrt( cx*cx + cy*cy + cz*cz);

   d  := -b00/r;

   fx := d*x + cz*vy - cy*vz;
   fy := d*y + cx*vz - cz*vx;
   fz := d*z + cy*vx - cx*vy;
   f  := Sqrt( fx*fx + fy*fy + fz*fz);

   p  := c*c/b00;
   e  := f/b00;
   i  := Ptan( Sqrt(cx*cx + cy*cy)/c, cz/c);

   if (i>eps) and (i<pi-eps) then omb := Ptan(cx/c, -cy/c)
                             else omb := 0.0;

   sincos( omb, so, co );
   ci := Cos(i);

   if Abs(i-pi/2)>eps then begin
      if f>eps then omm := Ptan( (fy*co - fx*so)/f/ci, (fy*so + fx*co)/f )
               else omm := 0.0;

      u := Ptan( (y*co - x*so)/r/ci, (y*so + x*co)/r);
   end
   else begin
      if f>eps  then omm := Ptan(fz/f, (fy*so + fx*co)/f)
                else omm := 0.0;

      u := Ptan(z/r, (y*so + x*co)/r);
   end
end{Kep_Par};


//============================================================
//============================================================
//============================================================
{-----------------------------------------------------------------------}
{             Расчет точки пересечения орбит                            }
{-----------------------------------------------------------------------}
procedure Toch_per(om, om_op, it, i_op: float;
                   var fi, fi_op, c: float);
var
  a, b, sa, sb, dom, cos_c, sin_c, sinfi, sinfi_op: float;
begin
   dom:=ABS(om - om_op);
   if dom<0.00001 then om := om_op;
   if om > om_op  then begin
      a := i_op;
      b := pi - it;
      sa := sin(a);
      sb := sin(b);
   end
   else begin
      a := it;
      b := pi - i_op;
      sa:= sin(b);
      sb:= sin(a);
   end;
   if om=om_op  then begin
      c     := 0;
      fi    := 0;
      fi_op := 0;
   end
   else begin
      cos_c := -cos(a)*cos(b) + sin(a)*sin(b)*cos(dom);
      sin_c :=  sqrt(1 - cos_c*cos_c);
      c     :=  Ptan(sin_c, cos_c);

      sinfi    := sin(dom)*sa/sin_c;
      sinfi_op := sin(dom)*sb/sin_c;
      fi       := Ptan(sinfi, sqrt(1 - sinfi*sinfi));

      fi_op    := Ptan(sinfi_op, sqrt(1 - sinfi_op*sinfi_op));
   end;
END;{ Toch_per }

//============================================================
//============================================================
//============================================================
{------------------------------------------------------------------------}
procedure XYZ( r, u, si, ci, sOm, cOm :float; var x,y,z : float);
var su,cu : float;
begin
   sincos(u, su, cu);
   x := r*(cOm*cu - sOm*ci*su);
   y := r*(sOm*cu + cOm*ci*su);
   z := r*su*si;
end;

//============================================================
//============================================================
//============================================================
{======================================================================}
function Gamma(mx, my, mz, nx, ny, nz, x, y, z: float): float;
var cg, d : float;
begin
   cg := (mx*nx + my*ny + mz*nz)
         /sqrt(mx*mx + my*my + mz*mz) /sqrt(nx*nx + ny*ny + nz*nz);
   d  :=  x*(my*nz - ny*mz);
   d  := d + y*(mz*nx - nz*mx);
   d  := d + z*(mx*ny - nx*my);

   if d>0 then Gamma :=  arccos(cg)
          else Gamma := -arccos(cg)
end;

//============================================================
//============================================================
//============================================================
{----------------------------------------------------------------}
{              Проверка функции на выпуклость                    }
{----------------------------------------------------------------}
function VIP(f1, f2, f3: float): integer;
var dl, dg: float;
begin
   dl := f1 - f2;
   dg := f3 - f2;
   if (dl>=0) and (dg>=0) and (dl + dg>=0) then vip := 1
                                           else vip := 0;
end; { VIP }

{--------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{---------------------------------------------------------------------}

procedure AgskToAosk(x,y,z,Vx,Vy,Vz : float; var MC : matr3_3);
var
   c1, c2, c3, c,
   b1, b2, b3, b, r, v: float;
begin
   r := Sqrt( x*x + y*y + z*z );
//   v := Sqrt( Vx*Vx + Vy*Vy + Vz*Vz );

   c1 := z*Vy - y*Vz;
   c2 := x*Vz - z*Vx;
   c3 := y*Vx - x*Vy;
   c  := Sqrt( c1*c1 + c2*c2 + c3*c3);
   b  := c*r;
   b1 := c3*y - c2*z;
   b2 := c1*z - c3*x;
   b3 := c2*x - c1*y;

   Mc[1,1] := b1/b;
   Mc[1,2] := x/r;
   Mc[1,3] := c1/c;
   Mc[2,1] := b2/b;
   Mc[2,2] := y/r;
   Mc[2,3] := c2/c;
   Mc[3,1] := b3/b;
   Mc[3,2] := z/r;
   Mc[3,3] := c3/c;
end{AgskToAosk};

{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

procedure KepToAgsk(i, omb, p, e, omm, u:float;
                    var x, y, z, Vx, Vy, Vz:float);
var
  a, c, r, vr, vt, tt, su, cu, si, ci,
  sw, cw, so, co    : float;
begin
   tt := u - omm;
   c  := (1.0 + e*Cos(tt));
   r  := p/c;

   sincos(u, su, cu);

   sincos(i, si, ci);
   sincos(omm, sw, cw);
   sincos(omb, so, co);

   x := r*(co*cu - so*ci*su);
   y := r*(so*cu + co*ci*su);
   z := r* su*si;
   a := sqrt(b00/p);
   vr := a*e*sin(tt);
   vt := a*c;
   vx := vr*(co*cu - so*ci*su) - vt*(co*su + so*ci*cu);
   vy := vr*(so*cu + co*ci*su) - vt*(so*su - co*ci*cu);
   vz := vr*su*si + vt*cu*si;
end{KepToAgsk};

{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

procedure OrbToAgsk(i,omb,u:float; var MC : matr3_3);
var
   su, cu, si, ci,
   so, co: float;
begin
   sincos(u, su, cu);
   sincos(i, si, ci);
   sincos(omb, so, co);
   MC[1,1] := -co*su - so*cu*ci;
   MC[1,2] := -so*su + co*cu*ci;
   MC[1,3] :=  cu*si;
   MC[2,1] :=  co*cu - so*su*ci;
   MC[2,2] :=  so*cu + co*su*ci;
   MC[2,3] :=  su*si;
   MC[3,1] := -so*si;
   MC[3,2] :=  co*si;
   MC[3,3] := -ci;
end{OrbToAgsk};

{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

Procedure Orbit_pereh(p0, e0, w0, i0, Om0, u0      : float; //град., км.
                      dVr, dVn, dVb                : vec2;
                      j                            : byte;
                  var i_p, Om_p, p_p, e_p, w_p, u_p: float);

Const rad=pi/180.0;
      gra=180.0/pi;

var xA, yA, zA, VxA, VyA, VzA,
//    xA1, yA1, zA1, VxA1, VyA1, VzA1,
    dVxA, dVyA, dVzA: float;
    MC     : matr3_3;

begin
   KepToAgsk(i0*rad, om0*rad, p0*1000.0, e0, w0*rad, u0*rad,      xA, yA, zA, VxA, VyA, VzA);

   OrbToAgsk(i0*rad, om0*rad, u0*rad, MC);

   dVxa := dVr[j]*MC[2,1] + dVn[j]*MC[1,1] - dVb[j]*MC[3,1];
   dVya := dVr[j]*MC[2,2] + dVn[j]*MC[1,2] - dVb[j]*MC[3,2];
   dVza := dVr[j]*MC[2,3] + dVn[j]*MC[1,3] - dVb[j]*MC[3,3];

   Kep_Par(xA, yA, zA, vxA+dVxA, vyA+dVyA, vzA+dVzA, i_p, Om_p, p_p, e_p, w_p, u_p);

   i_p  := i_p *gra;
   Om_p := Om_p*gra;
   w_p  := w_p *gra;
   u_p  := u_p *gra;
   p_p  := p_p/1000.0;
end; { Orbit_pereh }


{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

Procedure Interval0(i1, i2, w1, w2 : float;
                    var A1, B1, C1, D1, A2, B2, C2, D2: float);
var du : float;
Begin
  du :=-89/90*abs(i2-i1) + 90;
  A1 := 360 - du - w1;
  B1 := 360 + du - w1;
  C1 := 180 - du - w2;
  D1 := 180 + du - w2;
  A2 := 180 - du - w1;
  B2 := 180 + du - w1;
  C2 := 360 - du - w2;
  D2 := 360 + du - w2;
End;{ Конец процедуры Interval0 }


{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

Procedure dVmin_point_const(p0, e0, w0, i0, Om0, tt0,
                            pk, ek, wk, ik, Omk, tt_prib0, chag1, eps_tt: float;
                            var ttk_min, dVmin : float);
{ Процедура расчета точки ttk_min на целeвой орбите,
  которой соответствует dVmin }
var x0, x1, x2, x3, f1, f2, f3,
    h, dl, dg, f20, dx, fi1, fi2, fi3, fi,
    dV1, dVr1, dVn1, dVb1, dV2, dVr2, dVn2, dVb2: float;
Begin
   x0 := tt_prib0;
   x1 := x0 - chag1;
   x2 := x0;
   x3 := x0 + chag1;
   h  := chag1;
   while (h>eps_tt) do begin
      By_Imp(p0, e0, w0, i0, Om0, tt0, pk, ek, wk, ik, Omk, x1,
             dV1, dVr1, dVn1, dVb1, dV2, dVr2, dVn2, dVb2, f1, fi1);
      By_Imp(p0, e0, w0, i0, Om0, tt0, pk, ek, wk, ik, Omk, x2,
             dV1, dVr1, dVn1, dVb1, dV2, dVr2, dVn2, dVb2, f2, fi2);
      By_Imp(p0, e0, w0, i0, Om0, tt0, pk, ek, wk, ik, Omk, x3,
             dV1, dVr1, dVn1, dVb1, dV2, dVr2, dVn2, dVb2, f3, fi3);

      while VIP(f1, f2, f3) = 0 do begin
         if f1<f3 then begin
            x3 := x2; x2 := x1;
            f3 := f2; f2 := f1;
            x1 := x2 - h;
            By_Imp(p0, e0, w0, i0, Om0, tt0, pk, ek, wk, ik, Omk, x1,
                   dV1, dVr1, dVn1, dVb1, dV2, dVr2, dVn2, dVb2, f1, fi1);
         end
         else begin
            x1 := x2;  x2 := x3;
            f1 := f2;  f2 := f3;
            x3 := x2 + h;
            By_Imp(p0, e0, w0, i0, Om0, tt0, pk, ek, wk, ik, Omk, x3,
                   dV1, dVr1, dVn1, dVb1, dV2, dVr2, dVn2, dVb2, f3, fi3);
         end;
      end;

      dl := f1 - f2;
      dg := f3 - f2;
      dx := h*(dl - dg)/2/(dl + dg);
      h  := h/10;
      x2 := x2 + dx;
      x1 := x2 - h;
      x3 := x2 + h;
   end;

   By_Imp(p0, e0, w0, i0, Om0, tt0, pk, ek, wk, ik, Omk, x2,
          dV1, dVr1, dVn1, dVb1, dV2, dVr2, dVn2, dVb2, f2, fi);

   dVmin   := f2;
   ttk_min := x2;
End;  { Конец процедуры dVmin_point_const }

{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

{ Процедура расчета интервалов [А1_new,В1_new], [А2_new,В2_new]
  и [C1_new,D1_new], [C2_new,D2_new] шириной L=2*chag0 (или L=0)
  на исходной и целeвой орбитах соответственно для каждого из восходяших
  узлов, содержащих глобальные минимумы dVmin1, dVmin2 }
Procedure  point_var(p0, e0, w0, i0, Om0, pk, ek, wk, ik, Omk,
                     chag0, chag1, cf_max, eps_tt, tt_prib0: float;
                var  tt_beg1, tt_fin1, tt_beg2, tt_fin2: float);

var A1, B1, C1, D1, A2, B2, C2, D2,
    dVmin1, dVmin2 : float;
    j,k : integer;
    tt_beg, tt_fin : vec2;

    ttk_min, dVmin, tt0: float;//????????????????????????????????????????????? //была глобальная переменная

Begin
  dVmin1 := 8e8;
  dVmin2 := 8e8;

  Interval0(i0, ik, w0, wk, A1, B1, C1, D1, A2, B2, C2, D2);

  k := ROUND((B1 - A1)/chag0) + 1;

  for j:=0 to k do begin
     tt0 := A1 + (B1 - A1)/k*j;

     point_const(p0, e0, w0, i0, Om0, tt0,
                 pk, ek, wk, ik, Omk, tt0,
                 C1, D1, chag1, cf_max, tt_fin[1], dVmin);

     dVmin_point_const(p0, e0, w0, i0, Om0, tt0,
                       pk, ek, wk, ik, Omk, tt_fin[1],
                       chag1, eps_tt, ttk_min, dVmin);
     {    writeln(' tt0=',tt0:9:1,' ttk_min=',ttk_min:9:7,'  dVmin=',dVmin:9:2);}
     if dVmin<dVmin1 then begin
        dVmin1  := dVmin;
        tt_beg1 := tt0;
        tt_fin1 := ttk_min;
     end;

     tt0:=A2 + (B2 - A2)/k*j;
     point_const(p0, e0, w0, i0, Om0, tt0,
                 pk, ek, wk, ik, Omk, tt0,
                 C2, D2, chag1, cf_max, tt_fin[2], dVmin);
     dVmin_point_const(p0, e0, w0, i0, Om0, tt0,
                       pk, ek, wk, ik, Omk, tt_prib0,
                       chag1, eps_tt, ttk_min, dVmin);
{    writeln(' tt0=',tt0:9:1,' ttk_min=',ttk_min:9:7,'  dVmin=',dVmin:9:2);}
     if dVmin<dVmin2 then begin
        dVmin2  := dVmin;
        tt_beg2 := tt0;
        tt_fin2 := ttk_min;
     end;
  end;
{  Clrscr;
  writeln(' tt_beg1=',tt_beg1:9:2,' tt_fin1=',tt_fin1:9:2,'  dVmin1=',dVmin1:9:2);
  writeln(' tt_beg2=',tt_beg2:9:2,' tt_fin2=',tt_fin2:9:2,'  dVmin2=',dVmin2:9:2);
}
end; { point_var }

{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

Procedure Opt_By_imp(p0, e0, w0, i0, Om0,
                     pk, ek, wk, ik, Omk,
                     chag0, chag1, cf_max, eps_tt, tt_prib0 : float;

                var  tt_start, tt_prib,
                     dVmin1, dVr1, dVn1, dVb1,
                     dVmin2, dVr2, dVn2, dVb2,
                     dVsum, fi : vec2);

var  dvmin, ttk_min, x0, x1, x2, x3, f1, f2, f3, h, dl, dg, f20, dx: float;
     j 					 : byte;
     tt_beg, tt_fin                      : vec2;

Begin
   Point_var(p0, e0, w0, i0, Om0,
             pk, ek, wk, ik, Omk,
             chag0, chag1, cf_max, eps_tt, tt_prib0,
             tt_beg[1], tt_fin[1], tt_beg[2], tt_fin[2]);

   for j:=1 to 2 do begin
      h  := chag0;
      x0 := tt_beg[j];
      x1 := x0 - h;
      x2 := x0;
      x3 := x0 + h;
      while (h>eps_tt) do begin
         dVmin_point_const(p0, e0, w0, i0, Om0, x1,
                           pk, ek, wk, ik, Omk, tt_fin[j], chag1, eps_tt,
                           ttk_min, dVmin);

         f1 := dVmin;
         dVmin_point_const(p0, e0, w0, i0, Om0, x2,
                           pk, ek, wk, ik, Omk, tt_fin[j], chag1, eps_tt,
                           ttk_min, dVmin);
         f2 := dVmin;

         tt_prib[j] := ttk_min;

         dVmin_point_const(p0, e0, w0, i0, Om0, x3,
                           pk, ek, wk, ik, Omk, tt_fin[j], chag1, eps_tt,
                           ttk_min, dVmin);
         f3 := dVmin;

         while VIP(f1, f2, f3)=0 do begin
            if f1<f3 then begin
               x3 := x2;     f3 := f2;
               x2 := x1;     f2 := f1;
               x1 := x2 - h;
               dVmin_point_const(p0, e0, w0, i0, Om0, x1,
                                 pk, ek, wk, ik, Omk, tt_fin[j], chag1, eps_tt,
                                 ttk_min, dVmin);
               f1 := dVmin;
            end
            else begin
               x1 := x2;            f1 := f2;
               x2 := x3;            f2 := f3;
               x3 := x2 + h;
               dVmin_point_const(p0, e0, w0, i0, Om0, x3,
                                 pk, ek, wk, ik, Omk, tt_fin[j], chag1, eps_tt,
                                 ttk_min, dVmin);
               f3 := dVmin;
            end;
         end;

         dl := f1 - f2;
         dg := f3 - f2;
         dx := h*(dl - dg)/2/(dl + dg);
         h  := h/7.0;
         x2 := x2 + dx;
         x1 := x2 - h;
         x3 := x2 + h;
      end;

      tt_start[j] := x2;
      By_Imp(p0, e0, w0, i0, Om0, x2,
             pk, ek, wk, ik, Omk, tt_prib[j],
             dVmin1[j], dVr1[j], dVn1[j], dVb1[j],
             dVmin2[j], dVr2[j], dVn2[j], dVb2[j],
             dVsum[j], fi[j]);
   end;
end; { Opt_By_Imp }

{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
(*
Procedure Opt_Troi_imp(p0, e0, w0, i0, Om0,
                       pk, ek, wk, ik, Omk : float;
                  var  tt_start, tt_prib,
                       dVmin1, dVr1, dVn1, dVb1,
                       dVmin2, dVr2, dVn2, dVb2,
                       dVsum,fi : vec2);

var p_p1, e_p1, w_p1, i_p1, Om_p1, u_p1,
    p_p2, e_p2, w_p2, i_p2, Om_p2, u_p2,
    alfa,
    W, dv1, dv2, dv3, eps_dW, dW, W_0  : float;
{    tt_start,tt_prib,dVmin1,dVr1,dVn1,dVb1,
    dVmin2,dVr2,dVn2,dVb2,dVsum,fi                       : vec2;
}
   j,k      : byte;
begin

    //Clrscr;
   eps_dW := 1.0;
   alfa   := 0.5;

   Opt_By_imp(p0, e0, w0, i0, Om0,
              pk, ek, wk, ik, Omk,
              tt_start, tt_prib,
              dVmin1, dVr1, dVn1, dVb1,
              dVmin2, dVr2, dVn2, dVb2,
              dVsum, fi);

   Orbit_pereh(p0, e0, w0, i0, Om0, w0 + tt_start[1], dVr1, dVn1, dVb1, 1,
               i_p1, Om_p1, p_p1, e_p1, w_p1, u_p1);
    // writeln(' i=',i_p1,' Om=',Om_p1,' p=',p_p1,' e=',e_p1,' w=',w_p1);
   dvr1[1] := -dvr1[1];
   dvn1[1] := -dvn1[1];
   dvb1[1] := -dvb1[1];

   Orbit_pereh(pk,ek,wk,ik,Omk,wk + tt_prib[1],dVr1,dVn1,dVb1,1,
     i_p1,Om_p1,p_p1,e_p1,w_p1,u_p1);
    // writeln(' i=',i_p1,' Om=',Om_p1,' p=',p_p1,' e=',e_p1,' w=',w_p1);

   for j:=1 to 2 do begin
      k := 0;
      dVr1[j] := alfa*dVr1[j];
      dVn1[j] := alfa*dVn1[j];
      dVb1[j] := alfa*dVb1[j];
      {    dVr1[j]:=0;
           dVn1[j]:=00.0;
           dVb1[j]:=000.0;}
      Orbit_pereh(p0,e0,w0,i0,Om0,w0 + 0,dVr1,dVn1,dVb1,j,
                  i_p1,Om_p1,p_p1,e_p1,w_p1,u_p1);
       {writeln(' gm=',arccos(cos(i0*rad)*cos(i_p1*rad)+sin(i0*rad)*sin(i_p1*rad)*cos((om0-Om_p1)*rad))*gra:8:3);}
       //writeln(' i=',i_p1,' Om=',Om_p1,' p=',p_p1,' e=',e_p1,' w=',w_p1);
       {Writeln(' 1-> ',tt_start[1]:6:2,' ',dVsum[1]:6:2,' ',dVmin1[1]:6:2,' ',dVmin2[1]:6:2,
             dVr1[1]:6:2,' ',dVn1[1]:6:2,' ',dVb1[1]:6:2,dVr2[1]:6:2,' ',dVn2[1]:6:2,' ',dVb2[1]:6:2);
        Writeln(' 2-> ',tt_start[2]:6:2,' ',dvsum[2]:6:2,' ',dVmin1[2]:6:2,' ',dVmin2[2]:6:2,
               dVr1[2]:6:2,' ',dVn1[2]:6:2,' ',dVb1[2]:6:2,dVr2[2]:6:2,' ',dVn2[2]:6:2,' ',dVb2[2]:6:2);
        Writeln(' dv1a=',sqrt(sqr(dvr1[1])+sqr(dvn1[1])+sqr(dvb1[1])):6:2,
             ' dv2a=',sqrt(sqr(dvr1[2])+sqr(dvn1[2])+sqr(dvb1[2])):6:2);
        Writeln(' dv1b=',sqrt(sqr(dvr2[1])+sqr(dvn2[1])+sqr(dvb2[1])):6:2,
             ' dv2b=',sqrt(sqr(dvr2[2])+sqr(dvn2[2])+sqr(dvb2[2])):6:2);
        writeln(' i=',i_p1,' Om=',Om_p1,' p=',p_p1,' e=',e_p1,' w=',w_p1);}
      dV1 := sqrt( sqr(dVr1[j]) + sqr(dVn1[j]) + sqr(dVb1[j]) );
      Opt_By_imp(p_p1,e_p1,w_p1,i_p1,Om_p1,pk,ek,wk,ik,Omk,
                 tt_start,tt_prib,dVmin1,dVr1,dVn1,dVb1,
                 dVmin2,dVr2,dVn2,dVb2,dVsum,fi);
        {    dVr1[1]:=8.278;
             dVn1[1]:=2413.197;
             dVb1[1]:=-369.716;
             tt_start[1]:=359.958*rad;
              fi[1]:=180.04*rad;
           }
      Orbit_pereh(p_p1,e_p1,w_p1,i_p1,Om_p1,w_p1 + tt_start[j],dVr1,dVn1,dVb1,j,
                  i_p2,Om_p2,p_p2,e_p2,w_p2,u_p2);
       //writeln('  r 2=',p_p2/(1+e_p2*cos((u_p2+fi[j]-w_p2)*rad)):9:2);

      Orbit_pereh(p_p1,e_p1,w_p1,i_p1,Om_p1,w_p1 + tt_start[j+1],dVr1,dVn1,dVb1,j+1,
                  i_p2,Om_p2,p_p2,e_p2,w_p2,u_p2);
        //writeln('  r 2=',p_p2/(1+e_p2*cos((u_p2+fi[j]-w_p2)*rad)):9:2);
      dV2 := dVmin1[j];
      dV3 := dVmin2[j];
      dW  := 9e9;
        //writeln(' 0-я итер  dV=',(dv1 + dv2 + dv3):6:3,'   dv1=',dV1:6:3,'   dv2=',dV2:6:3,'   dv3=',dV3:6:3);
      while dW>eps_dW do begin
         Opt_By_imp(p0,e0,w0,i0,Om0,p_p2,e_p2,w_p2,i_p2,Om_p2,
                    tt_start,tt_prib,dVmin1,dVr1,dVn1,dVb1,
                    dVmin2,dVr2,dVn2,dVb2,dVsum,fi);
         W   := dVmin1[j] + dVmin2[j] + dV3;
         dV1 := dVmin1[j];
         k   := k + 1;
          //writeln(k:2,'-я итер  dV=',W:6:3,'   dv1=',dVmin1[j]:6:3,'   dv2=',dVmin2[j]:6:3,'   dv3=',dV3:9:3);
         Orbit_pereh(p0,e0,w0,i0,Om0,w0 + tt_start[j],dVr1,dVn1,dVb1,j,
                     i_p1,Om_p1,p_p1,e_p1,w_p1,u_p1);

         Opt_By_imp(p_p1,e_p1,w_p1,i_p1,Om_p1,pk,ek,wk,ik,Omk,
                    tt_start,tt_prib,dVmin1,dVr1,dVn1,dVb1,
                    dVmin2,dVr2,dVn2,dVb2,dVsum,fi);
         W_0:=dV1 + dVmin1[j] + dVmin2[j];
         dV3:= dVmin2[j];
         k:=k + 1;
          //writeln(k:2,'-я итер  dV=',W_0:6:3,'   dv1=',dV1:6:3,'   dv2=',dVmin1[j]:6:3,'   dv3=',dVmin2[j]:6:3);
         Orbit_pereh(p_p1,e_p1,w_p1,i_p1,Om_p1,w_p1 + tt_start[j],dVr1,dVn1,dVb1,j,
                     i_p2,Om_p2,p_p2,e_p2,w_p2,u_p2);
         dW:=abs(W_0 - W);
      end;
   end;
end; { Opt_Troi_imp }
*)
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

PROCEDURE PLT_2I(ArgP_u, Anom_u, ArgP_k, Anom_k, Fpar_u, Fpar_k, Exsc_u, Exsc_k,
                 Vosh_u, Vosh_k, Nakl_u, Nakl_k: float;

                 out DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a: float );

 (*     Расчет двухимпульсного перелета
  ArgP_u, Anom_u - аргумент перигея и истинная аномалия исходной орбиты, град
  ArgP_k, Anom_k - аргумент перигея и истинная аномалия конечной орбиты, град
  Fpar_u, Fpar_k - фокальный параметр, км.
  Exsc_u, Exsc_k - эксцентриситет нач. и исх. орб.
  Vosh_u, Vosh_k - прямое восхождение, град
  Nakl_u, Nakl_k - наклонение, град
 *)

LABEL 5,6;

var
    amin, amax,
    Args_u, Args_k, // угловая широта начальной и конечной точки
    modR_u, modR_k, // модули радиус векторов нач и конечной точки
    b, c, d, e, f, g,
    cos_D, sin_D, D_12,
    sin_A1, cos_A1, A_1,
    cos_A2, sin_A2, A_2,
    F_u, F_k,
    a1,
    Bpol_n1, Bpol_n2,  Bpol_min,
    Vr_u{m/c}, Vr_k, Vn_u, Vn_k
    : float;

    i: word;
    k, j: integer;
    R_u,R_k,r:ARRAY[1..3] OF float;
    Normal:ARRAY[1..3,1..3] OF float;
    x, y, XRe: v10;

BEGIN
   (* Аргументы широты исходной и конечной точек *)
   Args_u := ArgP_u + Anom_u;
   N360(Args_u);    //град
   Args_k := ArgP_k + Anom_k;
   N360(Args_k);    //град

    (* Модули радиусов-векторов исходной и конечной точек *)
   a1 := degtorad(Anom_u);
   modR_u := Fpar_u*1.0E3 /(1.0 + Exsc_u*COS(a1));
   a := degtorad(Anom_k);
   modR_k := Fpar_k*1.0E3 /(1.0 + Exsc_k*COS(a));

    (* Орт радиуса-вектора и нормаль к исходной орбите *)
   a := degtorad(Args_u);
   b := degtorad(Vosh_u);
   c := degtorad(Nakl_u);

   R_u[1] := COS(a)*COS(b) - SIN(a)*SIN(b)*COS(c);
   R_u[2] := SIN(a)*SIN(c);
   R_u[3] := COS(a)*SIN(b) + SIN(a)*COS(b)*COS(c);

   Normal[1,1] :=  SIN(b)*SIN(c);
   Normal[1,2] :=  COS(c);
   Normal[1,3] := -COS(b)*SIN(c);

    (*GOTOXY(1,1);
    WRITELN('Орт радиуса и нормаль исходной');
    WRITELN(R_u[1]:5:2,'   ',R_u[2]:5:2,'   ',R_u[3]:5:2);
    WRITELN(Normal[1,1]:5:2,'   ',Normal[1,2]:5:2,'   ',
            Normal[1,3]:5:2);*)

    (* Орт радиуса-вектора и нормаль к конечной орбите *)
    a := degtorad(Args_k);
    b := degtorad(Vosh_k);
    c := degtorad(Nakl_k);

    R_k[1] := COS(a)*COS(b) - SIN(a)*SIN(b)*COS(c);
    R_k[2] := SIN(a)*SIN(c);
    R_k[3] := COS(a)*SIN(b) + SIN(a)*COS(b)*COS(c);
    Normal[2,1] :=  SIN(b)*SIN(c);
    Normal[2,2] :=  COS(c);
    Normal[2,3] := -COS(b)*SIN(c);
    (*GOTOXY(40,1);
    WRITELN('Орт радиуса и нормаль конечной');
    GOTOXY(40,2);
    WRITELN(R_k[1]:5:2,'   ',R_k[2]:5:2,'   ',R_k[3]:5:2);
    GOTOXY(40,3);
    WRITELN(Normal[2,1]:5:2,'   ',Normal[2,2]:5:2,'   ',
            Normal[2,3]:5:2);*)

    (* Нормаль к переходной орбите и угловая дальность *)
    (* Угол измеряется против часовой стрелки (вид сверху)*)
    Normal[3,1] := R_k[2]*R_u[3] - R_k[3]*R_u[2];
    Normal[3,2] := R_k[3]*R_u[1] - R_k[1]*R_u[3];
    Normal[3,3] := R_k[1]*R_u[2] - R_k[2]*R_u[1];

    a:=0.0;
    FOR i := 1 TO 3 DO a := a + sqr(Normal[3,i]);
    a := SQRT(a);

    IF (a < 1.0E-20) THEN BEGIN
      cos_D := 1.0;
      sin_D := 0.0;
      D_12  := 0.0;

      VZLET(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k,
            DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a);
      GOTO 6
    END;
    //================================================

    FOR i := 1 TO 3 DO  Normal[3,i] := Normal[3,i] /a;

    IF (Normal[1,2]*Normal[2,2]) > 0.0 THEN
       IF (Normal[1,2]*Normal[3,2]) < 0.0 THEN
          FOR i := 1 TO 3 DO Normal[3,i]:=-Normal[3,i];

{    Normal[3,1] := -Normal[3,1];
    Normal[3,2] := -Normal[3,2];
    Normal[3,3] := -Normal[3,3];
}
    a:=0.0;
    FOR i := 1 TO 3 DO a := a + R_u[i]*R_k[i];

    IF a>1.0  THEN a :=  1.0;
    IF a<-1.0 THEN a := -1.0;
    cos_D := a;

    sin_D := SQRT(1.0-sqr(cos_D));

    a := (R_k[2]*Normal[3,3] - R_k[3]*Normal[3,2]) *R_u[1] +
         (R_k[3]*Normal[3,1] - R_k[1]*Normal[3,3]) *R_u[2] +
         (R_k[1]*Normal[3,2] - R_k[2]*Normal[3,1]) *R_u[3];

    IF a > 0.0 THEN sin_D := -sin_D;

    D_12 := ATN360(sin_D, cos_D);

    IF (ABS(D_12 - 180.0) < 1.0E-3) THEN BEGIN
       IF modR_u < modR_k THEN FOR i := 1 TO 3 DO  Normal[3,i] := Normal[1,i]
       ELSE           	       FOR i := 1 TO 3 DO  Normal[3,i] := Normal[2,i]
    END;

    IF (ABS(D_12) < 1.0E-3) OR (ABS(D_12-360.0) < 1.0E-3) THEN BEGIN
      cos_D := 1.0;
      sin_D := 0.0;
      D_12  := 0.0;
      VZLET(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k,
            DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a);
      GOTO 6
    END;
    //================================================
    (*GOTOXY(1,4);
    WRITE('Нормаль переходной :      ');
    WRITELN(Normal[3,1]:5:2,'   ',Normal[3,2]:5:2,'   ',
            Normal[3,3]:5:2);
    WRITELN('Угловая дальность перелета  :':29,D_12:7:2);*)
//  fi = d_12; //&&&&&&&&??????????????????????????????????????????????????????????????????????????????????
      (* Угол между исходной и переходной орбитами *)
      (* Измеряется в направлении увеличения накло-*)
      (* нения или восхождения восходящего узла    *)

    a:=0.0;

    FOR i := 1 TO 3 DO a := a + Normal[1,i]*Normal[3,i];

    IF a>1.0  THEN a :=  1.0;
    IF a<-1.0 THEN a := -1.0;

    cos_A1 := a;
    sin_A1 := SQRT(1.0 - sqr(cos_A1) );

    r[1] := Normal[3,2]*Normal[1,3] - Normal[3,3]*Normal[1,2];
    r[2] := Normal[3,3]*Normal[1,1] - Normal[3,1]*Normal[1,3];
    r[3] := Normal[3,1]*Normal[1,2] - Normal[3,2]*Normal[1,1];

    a := 0.0;
    FOR i := 1 TO 3 DO a := a + r[i]*R_u[i];

    IF a < 0.0 THEN sin_A1 := -sin_A1;

    A_1 := ATN360(sin_A1, cos_A1);

      (* Угол между переходной и конечной орбитами *)
      (* Измеряется в направлении увеличения накло-*)
      (* нения или восхождения восходящего узла    *)
    a := 0.0;
    FOR i := 1 TO 3 DO a := a + Normal[2,i]*Normal[3,i];
    cos_A2 := a;

    IF abs(1-sqr(cos_A2)) < 1e-10 THEN sin_A2 := 0.0
                                ELSE sin_A2 := SQRT(1.0 - sqr(cos_A2));

    r[1] := Normal[2,2]*Normal[3,3] - Normal[2,3]*Normal[3,2];
    r[2] := Normal[2,3]*Normal[3,1] - Normal[2,1]*Normal[3,3];
    r[3] := Normal[2,1]*Normal[3,2] - Normal[2,2]*Normal[3,1];

    a := 0.0;
    FOR i := 1 TO 3 DO a := a + r[i]*R_k[i];

    IF a < 0.0 THEN sin_A2 := -sin_A2;

    A_2 := ATN360(sin_A2, cos_A2);


      (* Расчет минимальной большой полуоси переходной орбиты *)

    Bpol_min := (modR_u + modR_k + SQRT( sqr(modR_u) + sqr(modR_k) - 2.0*modR_u*modR_k*cos_D))/4.0;

          (* Решение уравнения 4-й степени *)
    KOEFF(modR_u{m}, modR_k, Fpar_u{km}, Fpar_k, Exsc_u, Exsc_k, Anom_u{deg}, Anom_k,
                sin_D, cos_D, cos_A1, cos_A2,

                F_u, F_k, a, b, c, d, e, f, Vr_u{m/c}, Vr_k, Vn_u, Vn_k);


    KVADRA(a, b, c, d, e, j, x, y, XRe);
    FOKPAR(cos_D, sin_D, modR_u, modR_k, Bpol_min, g, b);

    IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
                 F_u, F_k, Vn_u, Vn_k, Vr_k,

            a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k);


    amin := a;

    IF j=0 THEN BEGIN
      {WRITELN('РЕШЕНИЙ ЗАДАЧИ ПЕРЕЛЕТА НЕТ');}
       GOTO 6
    END ELSE BEGIN
       k := 0;
        (*      Отладочный вывод для минимальной большой полуоси
        WRITELN('¦ ','M',' ¦ 1¦',DVr_u:15:3,DVn_u:15:3,DVb_u:14:3,'¦',DV_u:15:3,'¦');
        WRITELN('¦   ¦ 2¦',DVr_k:15:3,DVn_k:15:3,DVb_k:14:3,'¦',DV_k:15:3,'¦');
        WRITELN('¦   ¦SU¦                                            ¦',a:15:3,'¦');
        WRITELN('+---+--+--------------------------------------------+---------------+');*)

       FOR i:=1 TO j DO BEGIN
          g := xre[i];

          IF g > 0.0 THEN BEGIN
             inc(k);

             POLUOS(g, cos_D, sin_D, modR_u, modR_k, Bpol_n1);

             FOKPAR(cos_D, sin_D, modR_u, modR_k, Bpol_n1, g, b);

             IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
                    F_u, F_k, Vn_u, Vn_k, Vr_k,

                    a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k);

	           c := a;
             d := g;
             g := b;

             IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
                  F_u, F_k, Vn_u, Vn_k, Vr_k,

                    a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k);

             IF a > c THEN BEGIN
	              g := d;
                IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
                       F_u, F_k, Vn_u, Vn_k, Vr_k,

                       a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k);
	           END;
             (*         Отладочный вывод по критерию минимума квадрата
              WRITELN('¦ ',i:1,' ¦ 1¦',DVr_u:15:3,DVn_u:15:3,DVb_u:14:3,'¦',DV_u:15:3,'¦');
              WRITELN('¦dV2¦ 2¦',DVr_k:15:3,DVn_k:15:3,DVb_k:14:3,'¦',DV_k:15:3,'¦');
              WRITELN('¦   ¦SU¦                                            ¦',a:15:3,'¦');
              WRITELN('+---+--+--------------------------------------------+---------------+');*)
          END

       END;

       IF k = 0 THEN BEGIN
          FOKPAR(cos_D, sin_D, modR_u, modR_k, Bpol_min, g, b);

          IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
                 F_u, F_k, Vn_u, Vn_k, Vr_k,

                 a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k);
	        GOTO 6;

           (*WRITELN('¦ ',i:1,' ¦ 1¦           Решений нет                      ¦               ¦');
           WRITELN('¦   ¦ 2¦           Решений нет                      ¦               ¦');
           WRITELN('+---+--+--------------------------------------------+---------------+');*)
       END

    END;

    amax := a;

      (* Поиск минимума суммарного импульса *)
      (*    методом половинного деления     *)
    IF amax < amin THEN BEGIN
       c        := amin;
       d        := Bpol_min;
       amin     := amax;
       Bpol_min := Bpol_n1;
       amax     := c;
       Bpol_n1  := d
    END;

    5:
     Bpol_n2 := (Bpol_n1 + Bpol_min)/2.0;
     FOKPAR(cos_D, sin_D, modR_u, modR_k, Bpol_n2, g, b);

     IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
            F_u, F_k, Vn_u, Vn_k, Vr_k,

            a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k);
     c := a;
     d := g;
     g := b;

     IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
            F_u, F_k, Vn_u, Vn_k, Vr_k,

            a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k);

     IF a > c THEN BEGIN
        g := d;

        IMPULS(f, g, Vr_u, sin_D, cos_D, sin_A1, cos_A1, sin_A2, cos_A2,
               F_u, F_k, Vn_u, Vn_k, Vr_k,

               a, DVr_u, DVn_u, DVb_u, DVb_k, DVr_k, DVn_k, DV_u, DV_k);
     END;

     IF ABS(amin - amax) > 0.1 THEN BEGIN
        IF a > amin THEN BEGIN
	         amax    := a;
	         Bpol_n1 := Bpol_n2
        END ELSE BEGIN
	         amax     := amin;
	         Bpol_n1  := Bpol_min;
           amin     := a;
	         Bpol_min := Bpol_n2
        END;
        GOTO 5
     END;
   6:
END; (* Конец процедуры PLT_2I *)

{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

Procedure point_const(p0, e0, w0, i0, Om0, tt0,
                      pk, ek, wk, ik, Omk, tt1, C, D, chag1, cf_max : float;
                      var ttsr, dVmin : float);
{ Процедура расчета интервала [C_new,D_new] шириной L=2*chag1 со срединой
  ttsr на целeвой орбите, содержащего dVmin }
Const rad = pi/180.0;
var cf, ttk, c1, s1, ci, fi,
    dV1, dVr1, dVn1, dVb1,
    dV2, dVr2, dVn2, dVb2, dVsum : float;
    j,k                          : integer;

//    c_new, d_new: float;
Begin
  dVmin := 9e9;
//  C_new := C;
//  D_new := D;
  ttsr  := (C + D)/2;
  c1    := cos((tt1 + w0)*rad);
  s1    := sin((tt1 + w0)*rad);
  ci    := cos((ik  - i0)*rad);

  k := ROUND( (D - C) /chag1 ) + 1;
  for j:=0 to k do begin
     ttk := C + (D - C)/k*j;
     cf  := c1*cos( (ttk + wk)*rad ) + s1*sin( (ttk + wk)*rad )*ci;
     if cf<cf_max then begin
      By_Imp(p0, e0, w0, i0, Om0, tt0,
             pk, ek, wk, ik, Omk, ttk,
             dV1, dVr1, dVn1, dVb1,
             dV2, dVr2, dVn2, dVb2, dVsum, fi);
      if dVsum<dVmin then
      begin
        dVmin := dVsum;
        ttsr  := ttk;
      end;
    end;
  end;
End;  { Конец процедуры point_const }

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

PROCEDURE By_Imp(p0, e0, w0, i0, Om0, tt0,
                 pk, ek, wk, ik, Omk, ttk : float;

                 var dV1, dVr1, dVn1, dVb1,
                     dV2, dVr2, dVn2, dVb2,     dVsum, fi : float);


BEGIN; { Начало процедуры By_Imp }

   PLT_2I(w0, tt0, wk, ttk, p0, pk, e0, ek, Om0, Omk, i0, ik,
          dVr1, dVr2, dVn1, dVn2, dVb1, dVb2, dV1, dV2, dVsum);

   {PLT_2I(ArgP_u, Anom_u, ArgP_k, Anom_k, Fpar_u, Fpar_k, Exsc_u, Exsc_k,
                 Vosh_u, Vosh_k, Nakl_u, Nakl_k: float;

                 out DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a: float );}
   dVsum:=dV1 + dV2;
END; { Конец процедуры By_Imp }
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
procedure OptOrbToOrb(ArgP_u, ArgP_k, Fpar_u, Fpar_k, Exsc_u, Exsc_k,
                      Vosh_u, Vosh_k, Nakl_u, Nakl_k: float;
                      out Anom_u, Anom_k, DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a: float);

var
    DVr_u0, DVr_k0, DVn_u0, DVn_k0, DVb_u0, DVb_k0, DV_u0, DV_k0,
    a00, a0, u0, uk, du, du0: float;

    f:textfile;
begin
//   assignfile(f, 'out.txt');
//   rewrite(f);
   Anom_u :=  -0.5;
   du0    :=   0.5;
   a      := 1e9999;
   a0     := a;
   a00    := a;
   repeat

//     if a<a00 then begin a00 := a; end;

     Anom_u := Anom_u + du0;

     du     :=   10.0;
     Anom_k :=  -10.0;
//     a      := 1e9999;
     repeat
        a0 := a;

        Anom_k := Anom_k + du;

        PLT_2I( ArgP_u, Anom_u, ArgP_k, Anom_k, Fpar_u, Fpar_k, Exsc_u, Exsc_k,
                Vosh_u, Vosh_k, Nakl_u, Nakl_k,
                DVr_u, DVr_k, DVn_u, DVn_k, DVb_u, DVb_k, DV_u, DV_k, a);
//        writeln(f, a,' ', Anom_u:7:2,' ', Anom_k:7:2);

//        if a00>a then writeln(f, a,' ', Anom_u:7:2,' ', Anom_k:7:2);

        if a<a00 then
        begin
          a00:=a;
          uk := anom_k;
          u0 := anom_u;
          DVr_u0 := DVr_u;
          DVr_k0 := DVr_k;
          DVn_u0 := DVn_u;
          DVn_k0 := DVn_k;
          DVb_u0 := DVb_u;
          DVb_k0 := DVb_k;
          DV_u0  := DV_u;
          DV_k0  := DV_k;
        end;

        if a0<a then du := -du/2;

     until (abs(du)<0.1);
//     until Anom_k>360;

//     if a00<a then du0 := -du0/2;
   until Anom_u>360;
//   until (abs(du0)<0.1);
//   closefile(f);

   a := a00;
   anom_k := uk;
   anom_u := u0;
   DVr_u := DVr_u0;
   DVr_k := DVr_k0;
   DVn_u := DVn_u0;
   DVn_k := DVn_k0;
   DVb_u := DVb_u0;
   DVb_k := DVb_k0;
   DV_u  := DV_u0;
   DV_k  := DV_k0;


end;
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}


procedure KeplerToAgeco( p, e, i, OmB, teta, OmM: float;
                     out x, y, z, Vx, Vy, Vz:  float);
const My  = 398600.44e9;
Var //p  {фокальный параметр},
    r  {радиус вектор точки},
    vt {трансверсальная абсолютная скорость},
    vr {радиальная абсолютная скорость},
    u, sU, cU  {угловая широта аппарата },
    MyP,
    sK4, cK4  {синус косинус Kep[4]},
    sK2, cK2,
    sK3, cK3
    : float;
begin
    u := (teta + OmM);
//    PrivUgla(u);

//    p := a * (1.0 - e*e);
    r := p /(1.0 + e*cos(teta));
    MyP := power(My/p, 0.5);
    SinCos(teta, sK4, cK4);
    Vr := MyP * e * sK4;
    Vt := MyP * (1.0 + e*cK4);
    SinCos(u, sU, cU);
    SinCos(i, sK2, cK2);
    SinCos(Omb, sK3, cK3);
    x := ( cU*cK3 - sU*cK2*sK3 );
    y := ( cU*sK3 + sU*cK2*cK3 );
    z := sU *sK2;
    Vx := Vr * x;
    Vy := Vr * y;
    Vz := Vr * z;

    x := r * x;
    y := r * y;
    z := r * z;
    vx := vx - Vt *( sU *cK3 + cU *cK2 *sK3 );
    vy := vy - Vt *( sU *sK3 - cU *cK2 *cK3 );
    vz := vz + Vt *cU *sK2;
end; //KeplerToAgeco

Procedure OskToAgesk(x, y, z, Vx, Vy, Vz, t, w, s: float;
                     out ax, ay, az: float);
// перевод из ОСК в АГЕСК
// по координатам и скоростям в АГЭСК, м или км.
// t- трансверсальное, w-бинормальное, s-радиальное
Var r, c, cx, cy, cz: float;
Begin
    r  := power(x*x + y*y + z*z, 0.5);
    cx := y*Vz - z*Vy;
    cy := z*Vx - x*Vz;
    cz := x*Vy - y*Vx;
    c  := power(cx*cx + cy*cy + cz*cz, 0.5);
    cx := cx / c;
    cy := cy / c;
    cz := cz / c;

    ax := t*(cy*z-cz*y)/r - w*cx + s*x/r;
    ay := t*(cz*x-cx*z)/r - w*cy + s*y/r;
    az := t*(cx*y-cy*x)/r - w*cz + s*z/r;
End;

procedure PrivUgla(var ugol: float);
begin
    ugol := ugol - trunc(ugol/2.0/pi)*2.0*pi;
    if ugol<0.0 then  ugol := ugol + 2.0*pi;
End;


procedure AgecoToKepler(x, y, z, Vx, Vy, Vz:  float;
                    out p, e, i, OmB, teta, OmM: float);
{   Kep = [a, e, i,
          OmB  - прямое восхождение восх узла,
          teta - истинная аномалия,
          OmM  - угловая широта перигея] - м, рад}
const My  = 398600.44e9;
Const
  eps = 1e-10;
Var
  cx, cy, cz, c,
  fx, fy, fz, f,
  sOmb, cOmb, si, ci,
  k,
//  p, {фокальный параметр}
  r, {радиус-вектор}
  v, {абс. скорость}
  u: {угловая широта точки}
  float;
begin
    r := power(x*x + y*y + z*z, 0.5);
    V := power(Vx*Vx + Vy*Vy + Vz*Vz, 0.5);
    k := r*v*v/my;

    cx := y*Vz - z*Vy;
    cy := z*Vx - x*Vz;
    cz := x*Vy - y*Vx;
    c  := power(cx*cx + cy*cy + cz*cz, 0.5);

    fx := -my*x/r + cz*Vy - cy*Vz;
    fy := -my*y/r + cx*Vz - cz*Vx;
    fz := -my*z/r + cy*Vx - cx*Vy;
    f  := power(fx*fx + fy*fy + fz*fz, 0.5);
// Вычисление геометрии орбиты
    p := c*c /My;
//    a := r /(2.0 - k);
    e := f / my;
// вычисление положения плоскости орбиты
    i := cz/c;
    if i> 1.0 then i :=  1.0;
    if i<-1.0 then i := -1.0;
    i := arccos(i);

    if (i>eps)and(i<pi - eps)
    then Omb := arctan2(cx, -cy)
    else Omb := 0.0;
    PrivUgla(Omb);

// Вычисление положения КА в плоскости орбиты
    sincos(Omb, sOmb, cOmb);
    sincos( i , si  , ci  );
    if (i>pi/4.0)and(i<3.0*pi/4.0) then
       u := arctan2( z /si,  x*cOmb + y*sOmb )
    else
        u := arctan2(
          ( y*cOmb - x*sOmb ) / ci,
            x*cOmb + y*sOmb);
    PrivUgla(u);

    If e = 0.0 then begin
      omM:=0.0; teta:=u;
    end else begin
      teta := Arctan2( power(p /My, 0.5) * ( x*vx + y*vy + z*vz ),
                        p-r);
      PrivUgla(teta);
      omM:= u - teta;
      PrivUgla(omM);
    end;

end; //AgecoToKepler




procedure KeoToNewKeo(p0, e0, i0, Omb0, Omm0, teta0, dvr, dvn, dvb:float;
                      out p, e, i, Omb, Omm, teta: float); overload;

var ax, ay, az, a, x, y, z, Vx, Vy, Vz:  float;

begin
   KeplerToAgeco( p0*1000, e0, degtorad(i0), degtorad(OmB0), degtorad(teta0), degtorad(OmM0),
                  x, y, z, Vx, Vy, Vz);
   OskToAgesk(x, y, z, Vx, Vy, Vz, dvn, dvb, dvr, ax, ay, az);
   vx := vx + ax;
   vy := vy + ay;
   vz := vz + az;
   AgecoToKepler(x, y, z, Vx, Vy, Vz, p, e, i, OmB, teta, OmM);
   p    := p/1000;
   i    := radtodeg(i);
   Omb  := radtodeg(Omb);
   Omm  := radtodeg(Omm);
   teta := radtodeg(teta);
end;



{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
procedure KeoToNewKeo(p0, e0, i0, Omb0, Omm0, dvr, dvn, dvb,
                      pk, ek, ik, Ombk, Ommk:float;
                      out p, e, i, Omb, Omm: float;
                      var tetak, teta0: float); overload;
// процедура поиска места приложения и выдичи второго импульса 2-х импульсного маневра
// 0 - индекс - параметры орбиты переходной орбиты
// k - индекс - параметры конечной орбиты
// без индекса - параметры орбиты получившейся после приложения импульса
// dvr, dvn, dvb - величина выдаваемого импульса в ОСК конечной орбиты
// tetak - вход :  ист аномалия приложения импульса на конечной орбите
//       - выход:  ист аномалия положения КА на орбите после импульса

// teta0 - вход :  ист аномалия положения КА на переходной орбите
//       - выход:  ист аномалия приложения импульса на переходной орбите

// углы в градусах, длины в км.


var ax, ay, az, a, x, y, z, Vx, Vy, Vz,
    xk, yk, zk, Vxk, Vyk, Vzk:  float;

begin
   KeplerToAgeco( pk*1000, ek, degtorad(ik), degtorad(OmBk), degtorad(tetak), degtorad(OmMk),
                  xk, yk, zk, Vxk, Vyk, Vzk);
   OskToAgesk(xk, yk, zk, Vxk, Vyk, Vzk, dvn, dvb, dvr, ax, ay, az);

   teta0 := calcTet(tetak, ek, pk, e0, p0);

   KeplerToAgeco( p0*1000, e0, degtorad(i0), degtorad(OmB0), degtorad(teta0), degtorad(OmM0),
                  x, y, z, Vx, Vy, Vz);
   if (sqr(x-xk)+sqr(y-yk)+sqr(z-zk))>1 then
   begin
     teta0 := - teta0;
     KeplerToAgeco( p0*1000, e0, degtorad(i0), degtorad(OmB0), degtorad(teta0), degtorad(OmM0),
                    x, y, z, Vx, Vy, Vz);
   end;

   vx := vx + ax;
   vy := vy + ay;
   vz := vz + az;
   AgecoToKepler(x, y, z, Vx, Vy, Vz, p, e, i, OmB, tetak, OmM);
   p    := p/1000;
   i    := radtodeg(i);
   Omb  := radtodeg(Omb);
   Omm  := radtodeg(Omm);
   tetak := radtodeg(tetak);
end;



{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}


function calcEb(tet, exc: float): float;
// расчет эксцентрической аномалии по истинной аномалии и эксцентриситету
// [рад]
var t: float;
begin
   t := 2.0 * arctan( sqrt( (1.0-exc) / (1.0+exc) ) * tan(tet/2.0));
   if t<0.0 then t := t + 2.0 * pi;

   while tan(tet/2.0) * tan(t/2.0)<0.0 do t := t + pi;
   if t > 2.0*pi then t := t - 2.0 * pi;
   calcEb := t;
end;


{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}

function calcDT(p, e, t0, t1, t_imp:float):float;
const My  = 398600.44e9;
var dt, a,e0,e1:float;
begin
   e0 := calcEb(t0, e);
   e1 := calcEb(t1, e);
   a := p/(1-e*e);
   DT := sqrt(a*a*a/my) * ( e1 - e0 - e*(sin(e1) - sin(e0)) );

   if DT < 0 then
   DT := DT + 2*pi*sqrt(a*a*a/my);
   if dt < t_imp  then
   DT := DT + 2*pi*sqrt(a*a*a/my);
   calcdt := dt;
end;
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
{-----------------------------------------------------------------------}
function calcTet(tet1, e1, p1, e2, p2: float):float;
// расчет величины ист аномалии из соотношения равенства величин векторов местоположения
begin
   if e2<>0 then calcTet :=
      180/pi*arccos( ( p2/p1*(1 + e1*cos(degtorad(tet1))) -1)/e2 )
   else calcTet := 1e5;
end;

procedure PConvToRound(var x: float);
begin
   if abs(x-round(x))<1e-10 then x := round(x);
end;

function ConvToRound( x: float): float;
begin
   if abs(x-round(x))<1e-10 then ConvToRound := round(x);
end;



end.
