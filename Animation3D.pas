unit Animation3D;

interface

uses
  Winapi.Windows, Winapi.Messages, System.SysUtils, System.Variants, System.Classes,
  Vcl.Graphics, Vcl.Controls, Vcl.Forms, Vcl.Dialogs, OpenGL, ParamOG, math,  StdCtrls,
   ExtCtrls, ComCtrls,  Menus, Vcl.Buttons,SchDU_2, Autors,Save;
type
  TForm2 = class(TForm)
    Panel1: TPanel;
    Button1: TButton;
    Timer1: TTimer;
    Button5: TButton;
    Panel2: TPanel;
    Label7: TLabel;
    Label12: TLabel;
    Label8: TLabel;
    RadioButton1: TRadioButton;
    RadioButton2: TRadioButton;
    Label9: TLabel;
    CheckBox4: TCheckBox;
    Label10: TLabel;
    Button4: TButton;
    Button6: TButton;
    Panel3: TPanel;
    Label4: TLabel;
    Label1: TLabel;
    CheckBox1: TCheckBox;
    CheckBox2: TCheckBox;
    Label2: TLabel;
    Label3: TLabel;
    CheckBox3: TCheckBox;
    CheckBox5: TCheckBox;
    Label11: TLabel;
    Panel4: TPanel;
    Label5: TLabel;
    Button2: TButton;
    Button3: TButton;
    Label6: TLabel;
    TrackBar1: TTrackBar;
    Label14: TLabel;
    Panel5: TPanel;
    Label15: TLabel;
    Button8: TButton;
    Button7: TButton;
    Button9: TButton;
    Button10: TButton;
    Label13: TLabel;
    procedure FormDestroy(Sender: TObject);
    procedure FormResize(Sender: TObject);
    procedure FormCreate(Sender: TObject);
    procedure PrepareImage(bmap: string);
    procedure SetDCPixelFormat (hdc : HDC);
    procedure Risovanie_Orbit(AGSK: Tmass2D);
    Procedure Init;
    procedure FormPaint(Sender: TObject);
    procedure ORB1;
    procedure FormMouseMove(Sender: TObject; Shift: TShiftState; X, Y: Integer);
    procedure Button1Click(Sender: TObject);
    procedure FormKeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure FormMouseWheelDown(Sender: TObject; Shift: TShiftState;
      MousePos: TPoint; var Handled: Boolean);
    procedure FormMouseWheelUp(Sender: TObject; Shift: TShiftState;
      MousePos: TPoint; var Handled: Boolean);
    procedure Button2Click(Sender: TObject);
    procedure Button3Click(Sender: TObject);
    procedure Timer1Timer(Sender: TObject);
    procedure TrackBar1Change(Sender: TObject);
    procedure FormMouseDown(Sender: TObject; Button: TMouseButton;
      Shift: TShiftState; X, Y: Integer);
    procedure FormMouseUp(Sender: TObject; Button: TMouseButton;
      Shift: TShiftState; X, Y: Integer);
    procedure Button4Click(Sender: TObject);
    procedure Button6Click(Sender: TObject);
    procedure Button5Click(Sender: TObject);
    procedure Button7Click(Sender: TObject);
    procedure Button8Click(Sender: TObject);
    procedure Button9Click(Sender: TObject);
    procedure Button10Click(Sender: TObject);
    procedure CheckBox1Click(Sender: TObject);
    procedure CheckBox2Click(Sender: TObject);
    procedure CheckBox3Click(Sender: TObject);
    procedure CheckBox5Click(Sender: TObject);


  private
    { Private declarations }
   DC: HDC;     //����� �� ��������  ����������
   hrc:HGLRC;   //������ �� �������� ��������������� OpenGL
   vLeft, vRight, vBottom, vTop, vNear, vFar : GLFloat;// ����������� ���������� ��� ��������� �����������
   AngelX,AngelY,AngelZ : GLFloat;// ����������� ���������� ��� ��������� �����������
   spd :integer; //����������� ���������� ��� �������� ����������� �����
   r, ugol1, ugol2 : Extended;
   start:boolean;



  public
    { Public declarations }

  end;
 const

  om3 = 7.29211579e-5;
  oblast   = 1;   //������������� ��� ��������� �������������� �������
  Setka    = 2;   //������������� ��� ��������� ������������ �����   List(5)
  orbit1   = 3;   //������������� ��� ��������� ������
  gee      = 4;
  Koord1   = 5;
  Zvezdy   = 6;
  KA1      = 7;
  KA2      = 8;
  orbit2   = 9;
  VISIR1    = 10;
  VISIR2    = 11;
var
  Form2: TForm2;
  cv,bz : integer;
  st, st1, zamena,   activ:boolean;
  tim1, tim2:extended;
  prosmotr,zemlya, clic:bool;
  MX, MY,k1,k2, k3, vremya1, vremya2, vremya :integer;

  WH, HW, MyScale, ShiftXP, ShiftYP: GLFloat;
  RollAngleX, RollAngleY, RollAngleZ: GLFloat;
  ShiftX, ShiftY, FocalLength: GLFloat;


implementation

{$R *.dfm}

uses Settings, vyhod, Nachalo;

procedure Tform2.SetDCPixelFormat (hdc : HDC);

 var
  pfd : TPixelFormatDescriptor;  // ������ ������� ��������
  nPixelFormat : Integer;        //  ���������� ��� �������� ������� ������� �������
 begin
  FillChar (pfd, SizeOf (pfd), 0);                //
  pfd.dwFlags  := PFD_DRAW_TO_WINDOW or PFD_SUPPORT_OPENGL or PFD_DOUBLEBUFFER;//��������� ������
  nPixelFormat := ChoosePixelFormat (hdc, @pfd);  // ������ ������� � ����������� ���������� ������� ��������
  SetPixelFormat (hdc, nPixelFormat, @pfd);       // ������������ ������� � ��������� ����������
 end;

procedure TForm2.Timer1Timer(Sender: TObject);
var
  int:integer;
  trv:boolean;
  x0, y0,z0,x1, y1,z1, xk, yk,zk, xk1, yk1,zk1,t1, t2,t, D,a,b,c, l,m,n,alpha,betta,gamma,xd, yd,zd,ass1, ass2:extended;
  Quadric:GLUquadricObj; //���������� ������� ������� �������
begin
  form2.Timer1.interval:=spd;
  if (k1=Hh) or (k2=Hh) then
  begin
    vremya:=0;
    k1:=0;
    k2:=0;
  end;
  glEnable(GL_DEPTH_TEST);// ��������� ����� �������
  glClear(GL_COLOR_BUFFER_BIT);
  Quadric:= gluNewQuadric;// �������� ������� ������� �������
  gluQuadricDrawStyle(Quadric,GLU_FILL);// ����������� ����� ������� ������� �������
  ugol1:=form1.grad(om3*vremya);
  ugol2:=form1.grad(om3*orbita2[0,k3]);

  //================ ��������� �� �1========================================

  vremya1:=trunc(orbita1[0,k1]);
  if  vremya= vremya1  then
  begin
  glNewList(KA1,GL_COMPILE);
    glPushAttrib(GL_CURRENT_BIT);
    glTranslated(orbita1[4,k1],orbita1[5,k1],orbita1[6,k1]);
     glRotated(-45, 0,0, 1);
    glRotated(k1*(-3), 0,1, 0) ; //�������� ��
    // ������� ����� ������� ��---------------------------
    glPushMatrix;
      glRotated(90, 1,0, 0);

      glcolor3f(0.7,0.7,0.7	);
      glucylinder(Quadric,0.05,0.001,0.015,32,4);

      // ������� �� ��-----------------------
      glPopMatrix;
        glTranslated(0,0.013,0);
        glRotated(270, 1,0, 0);
        for int := 0 to 4 do
        begin
          glRotated(72, 0,0, 1);
          glLineWidth(1);
          glColor3f(0.1, 0.0, 0.8);
          glBegin(GL_POLYGON);
            glVertex3f(0.01,  0.01, 0);
            glVertex3f(0.045,  0.01, -0.01);
            glVertex3f(0.045, -0.01, -0.01);
            glVertex3f(0.01, -0.01, 0);
          glEnd;
        end;
        glColor3f(1, 0.0, 0.0);
        gluSphere (Quadric, 0.01,4,2);
        // ������ �� ��-----------------------
        glTranslated(0,0,0.-0.026);
        glRotated(0, 0,1, 0);
        glRotated(0, 0,0, 1);
        for int := 0 to 4 do
        begin
          glRotated(72, 0,0, 1);
          glLineWidth(1);
          glColor3f(0, 0.0, 0.4);
          glBegin(GL_POLYGON);
            glVertex3f(0.01,  0.01,     0);
            glVertex3f(0.045,  0.01, 0.01);
            glVertex3f(0.045, -0.01, 0.01);
            glVertex3f(0.01, -0.01,     0);
          glEnd;
        end;
     glPopMatrix;
      // �������� ����� ������� ��----------------------

    glPushMatrix;

      glTranslated(orbita1[4,k1]+0.011,orbita1[5,k1]+0.011,orbita1[6,k1]);
       glRotated(-45, 0,0, 1);
      glRotated(k1*(-3), 0,1, 0);
      glRotated(90, 1,0, 0);

      glcolor3f(0.7,0.7,0.7);

      glucylinder(Quadric,0.0001,0.05,0.015,32,4);
    glPopMatrix;
   glPopAttrib;
  glEndList;
  k1:=k1+1;
  end;
  //================ ��������� �� �2========================================

   vremya2:=trunc(orbita2[0,k2]);

 //  form2.Label14.Caption:=intTostr(vremya);
  // form2.Label15.Caption:=intTostr(vremya2);
  if  vremya =  vremya2  then
  begin
  glNewList(KA2,GL_COMPILE);
    glPushMatrix;
      // ������ ����� �������� �� �2
      xd:= orbita2[4,k2]-orbita1[4,k1];
      yd:= orbita2[5,k2]-orbita1[5,k1];
      zd:= orbita2[6,k2]-orbita1[6,k1];
      alpha:=form1.Grad(ptan(yd,xd));
      betta:=form1.Grad(ptan(zd,sqrt(xd*xd+yd*yd)));

      glTranslated(orbita2[4,k2],orbita2[5,k2],orbita2[6,k2]);
      glRotated(alpha, 0,0, 1);
      glRotated(90-betta, 0,1, 0);

      glEnable(GL_LINE_SMOOTH); //��������� ������ ����������� �����                                     //
      glLineWidth(3); // ������������ ������� �����                                                      //
      //������ �� �2
      glcolor3f(1,0.5,1);
      glucylinder(Quadric,0.017,0.017,0.09,16,4);
      //����� �������-----------------------------------------------------
      glcolor3f(1,0.5,1);
      gluDisk(Quadric,0,0.017,16,4);
      //����� �������-----------------------------------------------------
      glTranslated(0,0,+0.090);
      glcolor3f(1,0.5,1);
      gluDisk(Quadric,0,0.017,16,4);
      //��������� �������-----------------------------------------------------
      glTranslated(0,0,-0.03);
      glPushMatrix;
       glRotated(-90, 1,0,0);
      glLineWidth(1);
      glColor3f(0, 0, 0.8);
      glBegin(GL_POLYGON);
        glVertex3f( 0.08,  0.02, 0);
        glVertex3f( 0.08, -0.02, 0);
        glVertex3f(-0.08, -0.02, 0);
        glVertex3f(-0.08,  0.02, 0);
      glEnd;
      glPopMatrix;
    glPopMatrix;
  glEndList;
  k2:=k2+1;
  end;

  //================ ��������� ����� �����������=================================
  trv:=false;
  glDeleteLists(visir1,1);
  glDeleteLists(visir2,1);

  if fokal1<fokal2 then
  begin
    x0:=orbita1[4,k1];
    y0:=orbita1[5,k1];
    z0:=orbita1[6,k1];
    x1:=orbita2[4,k2];
    y1:=orbita2[5,k2];
    z1:=orbita2[6,k2];
  end;
  if fokal1>fokal2 then
  begin
    x0:=orbita2[4,k1];
    y0:=orbita2[5,k1];
    z0:=orbita2[6,k1];
    x1:=orbita1[4,k2];
    y1:=orbita1[5,k2];
    z1:=orbita1[6,k2];
   end;

   l:= (x1-x0);
   m:= (y1-y0);
   n:= (z1-z0);

   a:=sqr(l)+sqr(m)+sqr(n);
   b:=2*(x0)*l+2*(y0)*m +2*(z0)*n ;
   c:=sqr(x0)+ sqr(y0)+sqr(z0)-sqr(0.6471) ;
   D:=(sqr(b)-4*a*c);

   if D>0 then
   begin
     t1:=(-b+sqrt(D))/2*a;
     t2:=(-b-sqrt(D))/2*a;

     xk:=x0+l*t1;
     yk:=y0+m*t1;
     zk:=z0+n*t1;

     xk1:=x0+l*t2;
     yk1:=y0+m*t2;
     zk1:=z0+n*t2;
   end;

   if (((x0-xk)*(x1-xk)+(y0-yk)*(y1-yk)+(z0-zk)*(z1-zk))<=0)
   or (((x0-xk1)*(xk-xk1)+(y0-yk1)*(y1-yk1)+(z0-zk1)*(z1-zk1))<=0)
   then  trv:=true else trv:=false;

   if   (D<0) or ((D>=0) and (trv=false)) then
   begin
     form2.Label13.Visible:=false;
     glNewList(VISIR1,GL_COMPILE);
       glEnable(GL_LINE_SMOOTH); //��������� ������ ����������� �����
       glLineWidth(1); // ������������ ������� �����
       glBegin(GL_LINES); ///Beg(1) ����� ��������� �����
         glColor3f(255.0,0.0,0.0);
         glVertex3f(orbita1[4,k1],orbita1[5,k1]+0.013,orbita1[6,k1]);
         glVertex3f(orbita2[4,k2],orbita2[5,k2]+0.013,orbita2[6,k2]);
       glEnd;
    glEndList;
  end;
  if  (D<0) or ((D>=0) and (trv=false))
   then begin
    form2.Label13.Visible:=false;
    glNewList(VISIR2,GL_COMPILE);

     glEnable(GL_LINE_SMOOTH); //��������� ������ ����������� �����
     glLineWidth(1); // ������������ ������� �����
     glBegin(GL_LINES); ///Beg(1) ����� ��������� �����
       glColor3f(255,0.0,0.0); //��� X
       glVertex3f(orbita1[4,k1],orbita1[5,k1],orbita1[6,k1]);
       glVertex3f(orbita2[4,k2],orbita2[5,k2],orbita2[6,k2]);
     glEnd;
   glEndList;
  end else form2.Label13.Visible:=true;

   vremya:= vremya+1;
   k3:=k3+1;
  gluDeleteQuadric(Quadric);  // �������� ������� ������� �������
  glDisable(GL_DEPTH_TEST);// ���������� ����� �������
  FormResize(nil);   //����������� ����� ���� ������
  xk:=0;
  yk:=0;
  yk:=0;
  xk1:=0;
  yk1:=0;
  zk1:=0;
  t1:=0;
  t2:=0;
  D:=0;

end;

procedure TForm2.TrackBar1Change(Sender: TObject);
begin
  spd:=(form2.TrackBar1.Max+1)-(form2.TrackBar1.Position);
end;

procedure Tform2.Risovanie_Orbit(AGSK: Tmass2D);
 var
  f:integer;
 begin
  //glPointSize(0.2);                     //������ �����                                           //
  //glEnable(GL_POINT_SMOOTH);            //��������� ����������� �����                            //
  glEnable(GL_LINE_SMOOTH); //��������� ����������� �����                                           //
  //glBegin(GL_POINTS); ///Beg(1) ����� ��������� ����� ------                                     //
  glBegin(GL_LINE_STRIP); ///Beg(1) ����� ��������� ����� ------                                    //

   glLineWidth(1);    //������������� ������� �����                                             //

   For f:=0 to Hh-1 do//���������� ����������� ����� ��� ��������� ������ //
   begin                                                                                         //
    glVertex3f(AGSK[4,f],AGSK[5,f],AGSK[6,f]);  //������ ����� ������//
   end;                                                                                          //
                                                                                                      //
  glEnd;
 end;

procedure TForm2.Button10Click(Sender: TObject);
begin
  form1.WindowState:=wsMinimized;
  form2.WindowState:=wsMinimized;
end;

procedure TForm2.Button1Click(Sender: TObject);
begin
  if zamena=true then form5.show else form6.show;
end;

procedure TForm2.Button2Click(Sender: TObject);
begin
  form2.Timer1.Enabled:=true;
   form2.RadioButton1.Enabled:=true;
  form2.RadioButton2.Enabled:=true;
  form2.trackbar1.Enabled:=true;

end;

procedure TForm2.Button3Click(Sender: TObject);
begin
  form2.Timer1.Enabled:=false;
  form2.RadioButton1.Enabled:=false;
  form2.RadioButton2.Enabled:=false;

  form2.trackbar1.Enabled:=false;
end;

procedure TForm2.Button4Click(Sender: TObject);
begin
  form3.Show;
end;

procedure TForm2.Button5Click(Sender: TObject);
begin
  form4.show;
end;

procedure TForm2.Button6Click(Sender: TObject);
begin
  form1.Ishodnye;
end;

procedure TForm2.Button7Click(Sender: TObject);
begin
  form1.Izvlechenie;

end;

procedure TForm2.Button8Click(Sender: TObject);
begin
  form1.Sohranenie;
  form2.Button7.Enabled:=true;
  form2.Button9.Enabled:=true;
  zamena:=false;
end;

procedure TForm2.Button9Click(Sender: TObject);
begin
  form1.sbros;
  form2.Button7.Enabled:=false;
  form2.Button9.Enabled:=false;
end;

procedure TForm2.CheckBox1Click(Sender: TObject);
begin
  zamena:=true;
  form2.Button8.Enabled:=true;
end;

procedure TForm2.CheckBox2Click(Sender: TObject);
begin
   zamena:=true;
   form2.Button8.Enabled:=true;
end;

procedure TForm2.CheckBox3Click(Sender: TObject);
begin
 zamena:=true;
 form2.Button8.Enabled:=true;
end;

procedure TForm2.CheckBox5Click(Sender: TObject);
begin
 zamena:=true;
 form2.Button8.Enabled:=true;
end;

procedure TForm2.FormCreate(Sender: TObject);
begin
    activ:=false;
  DC:= GetDC(Handle);       //  ���������� ������ �� ��������(����������) ����
  SetDCPixelFormat (DC);      // ��������� ������� ��������
  hrc := wglCreateContext(DC); // ���������� ������ �� �������� ��������������� OpenGL
  wglMakeCurrent(DC,hrc);      // ��������� �������� ���������
  glClearColor (0.0, 0.0, 0.0, 0); // ���� ����
  glViewport(0,trunc(ClientHeight/2-Clientwidth/2), Clientwidth, Clientwidth);    //����������� ������� ������
  Init; //����� ��������� �������������
  // ���������� ��������� �������� ��������� ��� ��������� ����������� -------------
  vLeft := -1;
  vRight := 1;
  vBottom := -1;
  vTop := 1;
  vNear := 2;   //3
  vFar := 10;
  // ���������� ��������� �������� ��������� ��� ��������� ���� �������� �����������-
  AngelX:= -60;
  AngelY:= 0  ;
  AngelZ:= 235;
  //---------------------------------------------------
  cv:=0;
  bz:=1;
  //SetLength(VKL,1) ;
  // VKL[0]:=0;
  st:=false;  st1:=true;
  clic:=false;  //���������� ��������� �������� ��������� ��� �������� ������� ������ ����

    if FileExists('Parametry.ini') then
  begin
    form2.Button7.Enabled:=true;
    form2.Button9.Enabled:=true;

  end;


end;

procedure TForm2.FormDestroy(Sender: TObject);
begin
  wglMakeCurrent(0, 0);   //��������� ���������
  wglDeleteContext(hrc);  //������� ��������� ��������������� OpenGL
  ReleaseDC (Handle, DC); //������� ��������� ����
  DeleteDC (DC);
end;

procedure TForm2.FormKeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key = ord ('A') then
  begin
   AngelZ := AngelZ + 1;
   FormResize(nil);   //��������� �����������
  end;

  If Key = ord ('D') then
  begin
   AngelZ := AngelZ - 1;
   FormResize(nil);
  end;

  If Key = ord ('S') then
  begin
   AngelX := AngelX + 1;
   FormResize(nil);
  end;

  If Key = ord ('W') then
   begin
   AngelX := AngelX - 1;
   FormResize(nil);
  end;

  If Key =ord ('Q') then
  begin
   AngelY := AngelY + 1;
   FormResize(nil);
   end;

  If Key = ord ('E')then
  begin
   AngelY := AngelY - 1;
   FormResize(nil);
  end;
   If (Key = 27) and  (zamena=true) then  form5.show;
    If (Key = 27) and  (zamena=false) then  form6.show;
end;

procedure TForm2.FormMouseDown(Sender: TObject; Button: TMouseButton;
  Shift: TShiftState; X, Y: Integer);
begin
   clic:=true;
  MX:=X;
  MY:=Y;
end;

procedure TForm2.FormMouseMove(Sender: TObject; Shift: TShiftState; X,
  Y: Integer);
var
  Xc,Yc,DeltaZ: Single;
begin

   if activ=false then  form7.show ;


  if X<174 then
   begin panel1.visible:=true;
     activ:=true;
      form7.close
  end
   else panel1.visible:=false;
  FormResize(nil);

   If Shift = [ssShift, ssLeft] then begin  { �������� ������ ��� Z }
  Xc:=trunc(form2.ClientWidth/2);
  Yc :=trunc(form2.ClientHeight/2);
  DeltaZ := form1.Rad(ArcTan2(Yc-Y, X-Xc) - ArcTan2(Yc-MY, MX-Xc));

  If Odd(Floor((AngelX +90)/180)) xor
      Odd(Floor((Angelz+90)/180)) then DeltaZ := -DeltaZ;
   AngelZ := AngelZ + DeltaZ;
   end
   else if Shift = [ssLeft] then begin { ������ ������ }
   AngelX := AngelX - (MY-Y)*0.1;
   Angelz := Angelz - (MX-X)*0.1;
   end else exit;
  MX := X;    MY := Y;
{ �������� ���������� ������ - �� ��������� 45�� }
  // FocalLength := Min(300, Max(10, FocalLength - (MY-Y)*0.1));
   FormResize(nil);
end;

procedure TForm2.FormMouseUp(Sender: TObject; Button: TMouseButton;
  Shift: TShiftState; X, Y: Integer);
begin
   clic:=false;
end;

procedure TForm2.FormMouseWheelDown(Sender: TObject; Shift: TShiftState;
  MousePos: TPoint; var Handled: Boolean);
begin
   vLeft := vLeft + 0.1;
  vRight := vRight - 0.1;
  vBottom := vBottom + 0.1;
  vTop := vTop - 0.1;
  FormResize(nil);
end;

procedure TForm2.FormMouseWheelUp(Sender: TObject; Shift: TShiftState;
  MousePos: TPoint; var Handled: Boolean);
begin
    vLeft := vLeft - 0.1;
  vRight := vRight + 0.1;
  vBottom := vBottom - 0.1;
  vTop := vTop + 0.1;
  FormResize(nil);
end;

procedure TForm2.FormPaint(Sender: TObject);
var
  i,j:integer;
begin
  glClear (GL_COLOR_BUFFER_BIT or GL_DEPTH_BUFFER_BIT);     // ������� ������ �����  � ������ �������
  glEnable (GL_BLEND);

  glPushMatrix;
    if checkbox3.Checked=true  then  glCallList(Koord1);  // ��������� ������������ ����
  glPopMatrix;

  if checkbox1.Checked=true then   //  �������� ������� ������� "�����"
    begin
      glPushMatrix;
        glcolor3f(1,1,1);
        glrotatef(89+ugol1,0,0,1);
        glCallList(Gee);             // ��������� �����
      glPopMatrix;
    end;

  if checkbox2.Checked=true then
  begin
    glPushMatrix;
      glrotatef(ugol1,0,0,1);
      glCallList(Setka);         // ��������� ��������
    glPopMatrix;
  end;
  if form2.RadioButton1.Checked then
  begin
    glCallList(visir1);
    form2.CheckBox4.Enabled:=false;
    form2.label10.Enabled:=false;
  end;

  if form2.RadioButton2.Checked  then
  begin
    form2.CheckBox4.Enabled:=true;
    form2.label10.Enabled:=true;
    if form2.CheckBox4.Checked=true then   glCallList(visir2);
  end;

  glPushMatrix;
    if form2.CheckBox5.Checked=true then
    begin
      glCallList(orbit1);
      glCallList(orbit2);
    end;
    glCallList(KA1);
    glCallList(KA2);
  glPopMatrix;
  glCallList(Zvezdy);
  SwapBuffers(DC);  // ���������� ������ - �� �����

end;

procedure TForm2.FormResize(Sender: TObject);
 type
  TLightPos = Array[0..3] of GLFloat;                        // ������ �������� ���������� ��������� �����
  TMaterial = Array[0..3] of GLFloat;
                   // ������ �������� �������� �������� ���������
 const
  //������� �������� ������������ ��������� �����
  Pos1:TLightPos = (3,3,0,0.01);   //  �������� ����� �0

 begin
  glEnable(GL_DEPTH_TEST);                                   // ��������� ����� �������
  glEnable(GL_LIGHTING);                                     //��������� ���������
  glEnable(GL_LIGHT0);                                       //���������� ��������� ��������� �����  �0
  // glEnable(GL_LIGHT1);                                     //���������� ��������� ��������� ����� �1
  glLightfv(GL_LIGHT0,GL_POSITION,@Pos1);
                    //����� ����� ������������ ��������� �����  �0
  //glLightfv(GL_LIGHT1,GL_POSITION,@Pos2);                  //����� ����� ������������ ��������� ����� �1
  glViewport(0,trunc(ClientHeight/2-Clientwidth/2), Clientwidth, Clientwidth);           //������� ��������� �����������
  gLMatrixMode (GL_PROJECTION);                              //������� � ������� ��������
  glLoadIdentity;
  glFrustum (vLeft, vRight, vBottom, vTop, vNear, vFar);     // ������ �����������
  // ���� �������� ����� ��� �������� �����������
  glMatrixMode(GL_MODELVIEW);                                //������� � ������� �������
  glLoadIdentity;
  glTranslatef(0.0, 0.0, -4.0);                              // ������� ������� - ��� Z
  glRotatef(AngelX, 1.0, 0.0, 0.0);                          // ������� ������� - ��� X
  glRotatef(AngelY, 0.0, 1.0, 0.0);                          // ������� ������� - ��� Y
  glRotatef(AngelZ, 0.0, 0.0, 1.0);                          // ������� ������� - ��� Z
  //����� ������ �������� ����������� � ������ �������
  {StatusBar1.Panels.Items[4].Text := '�������: ��� � = '+FloatToStr(AngelX)+
                                            ' ��� Y = '+FloatToStr(AngelY)+
                                            ' ��� Z= '+FloatToStr(AngelZ); }

  InvalidateRect(Handle, nil, False);                        //����������� �����������
end;

Procedure TForm2.Init;
type
  TMaterial = Array[0..3] of GLFloat;// ������ �������� �������� �������� ���������

const
  // ������� ������� �������� ������� ���������
  Mat1:TMaterial = (1,0,0,1);
  Mat2:TMaterial = (0,1,0,1);
  Mat3:TMaterial = (0,0,1,1);
  Mat4:TMaterial = (0,0,0.9,0.6);

var
  Quadric:GLUquadricObj;  //���������� ������� ������� �������
  lk3,w3, gs3:integer;
  fi,fir,h:extended;
  i,j: integer;
begin
  glEnable(GL_DEPTH_TEST);// ��������� ����� �������
  glEnable (GL_COLOR_MATERIAL); // ���������� ������� �������� ������� ���������
  glEnable(GL_AUTO_NORMAL);// �������������� ���������� �������
  Quadric:= gluNewQuadric;// �������� ������� ������� �������
  gluQuadricDrawStyle(Quadric,GLU_FILL);// ����������� ����� ������� ������� �������
  gluQuadricTexture (Quadric, 2);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
  glEnable(GL_TEXTURE_2D);
  glBlendFunc (GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
  //=========================��������� �����=============================================================
  glNewList(Gee,GL_COMPILE);

    prepareImage (ExtractFilePath(application.ExeName));
    glEnable(GL_CULL_FACE);

    glCullFace(GL_FRONT);
    gluSphere (Quadric, 0.6371,35,35);
    glCullFace(GL_BACK);
    gluSphere (Quadric, 0.6371,35,35);
    glDisable(GL_CULL_FACE);
    //   glDisable(GL_ALPHA_TEST);// ����������  ������ ������������                                        //
    glDisable(GL_BLEND);// ����������  ���������� ������                                               //glEndList;//List(2) ---------------------------------------------------------------------------------//
  glEndList;
  //======================================================================================
  // glDisable(GL_TEXTURE_2D);
  gluQuadricTexture (Quadric, 0);
  //=========================��������� ������������ ���� �����=============================================================
  glNewList(Koord1,GL_COMPILE); //List(1)//������ ������������ ���

    glEnable(GL_LINE_SMOOTH); //��������� ������ ����������� �����                                     //
    glLineWidth(1); // ������������ ������� �����                                                      //
    glBegin(GL_LINES); ///Beg(1) ����� ��������� �����                                                 //
      glColor3f(1.0,0.0,0.0); //��� X                                                                  //
      glVertex3f(0,0,0);                                                                               //
      glVertex3f(0.9,0,0);                                                                             //
      glColor3f(0.0,1,0.0); //��� Y                                                                    //
      glVertex3f(0,0,0);                                                                               //
      glVertex3f(0,0.9,0);                                                                             //
      glColor3f(0.0,0.0,1.0); //��� z                                                                  //
      glVertex3f(0,0,0);                                                                               //
      glVertex3f(0,0,0.9);                                                                             //
    glEnd; ///Beg(1)                                                                                   //
                                                                                                            //
          // glPolygonMode (GL_FRONT_AND_BACK, GL_LINE); // ����� ����������� ���������(������)              //
    glPushMatrix;//(1)--------------- ����� �� ��� X                                                   //
      glTranslated(0.9,0,0);                                                                           //
      glRotatef(90,0,1,0);                                                                             //
      glMaterialfv(GL_FRONT_AND_BACK,GL_DIFFUSE,@Mat1); //���������� �������� ��������� ���������      //
      glColor3f(1,0,0);                                                                                //
      gluCylinder(Quadric,0.03,0,0.1,15,15);                                                           //
    glPopMatrix; //(1)---------------                                                                  //
                                                                                                             //
    glPushMatrix;//(1)--------------- ����� �� ��� Y                                                   //
      glTranslated(0,0.9,0);                                                                           //
      glRotatef(-90,1,0.0,0);                                                                          //
      glMaterialfv(GL_FRONT_AND_BACK,GL_AMBIENT,@Mat2); //���������� �������� ��������� ���������      //
      glColor3f(0,1,0);                                                                                //
      gluCylinder(Quadric,0.03,0,0.1,15,15);                                                           //
    glPopMatrix; //(1)---------------                                                                  //
                                                                                                            //
    glPushMatrix;//(1)--------------- ����� �� ��� Z                                                   //
      glTranslated(0,0,0.9);                                                                           //
      glRotatef(90,0,0,1);                                                                             //
      glMaterialfv(GL_FRONT_AND_BACK,GL_DIFFUSE,@Mat3); //���������� �������� ��������� ���������               //
      glColor3f(0,0,1);                                                                                //
      gluCylinder(Quadric,0.03,0,0.1,15,15);                                                           //
    glPopMatrix; //(1)---------------

    glDisable(GL_LINE_SMOOTH);// ���������� ������ ����������� �����                                   //
  glEndList;
   //==================��������� ����. ����� ==================================================
  glNewList(Setka,GL_COMPILE);
    glrotatef(90,1,0,0);
    //��������� ��������--------------------------------------------------------------
    for i:=0  to 17 do
    begin
      glPushMatrix;
        glrotatef(10*i,0,1,0);
        glColor3f(1,0.5,1);
        glucylinder(Quadric,0.64,0.64,0.001,40,15);  // ���������
      glPopMatrix;
    end;
    // ������� ��������
    glColor3f(1,0,0);
    glucylinder(Quadric,0.64,0.64,0.005,40,15);
    glPopMatrix;
    //��������� ����� �����------------------------------------------------------------
    for j := 0 to 9 do
    begin
      glPushMatrix;
        fi:=j*10;
        fir:=fi*pi/180;
        h:=6471*sin(fir);
        r:=6471*cos(fir);
        glTranslated(0,0,h/10000);
        glColor3f(0.1,1,1);
        glucylinder(Quadric,r/10000,r/10000,0.001,40,15);
      glPopMatrix;
    end;
    //��������� ����� ����-------------------------------------------------------
    for j:=0 to 9 do                                                                         //
    begin
      glPushMatrix;
        fi:=j*(-10);
        fir:=fi*pi/180;
        h:=6400*sin(fir);
        r:=6400*cos(fir);                                             //  ������ ����
        glTranslated(0,0,h/10000);
        glColor3f(0.1,1,1);
        glucylinder(Quadric,r/10000,r/10000,0.001,40,15);
      glPopMatrix;
    end;
    //---------------------------------------------------------------------------------
    glPushMatrix;
      glColor3f(1,0,0);
      glucylinder(Quadric,0.64,0.64,0.005,40,15);   // �������
    glPopMatrix;
  glEndList;
   //��������� �����/////////////////////////////////////////////////////////////////
  glNewList (Zvezdy, GL_COMPILE);
    glPushMatrix;
      glScalef(1, 1, 1);
      glEnable(gl_point_smooth);
      glPointSize (3);
      glColor4f (1, 1, 1, 1.0);
      glBegin (GL_POINTS);
        randomize;
        for i := 1 to 1500 do
        begin
          glVertex3f( random*20,  random*20,  random*20);
          glVertex3f(-random*20,  random*20,  random*20);
          glVertex3f( random*20, -random*20,  random*20);
          glVertex3f( random*20,  random*20, -random*20);
          glVertex3f(-random*20, -random*20,  random*20);
          glVertex3f( random*20, -random*20, -random*20);
          glVertex3f(-random*20,  random*20, -random*20);
          glVertex3f(-random*20, -random*20, -random*20);
        end;
      glEnd;
      glScalef(1, 1, 1);
    glPopMatrix;
  glEndList;

  ugol1:=0;
  spd:=form2.TrackBar1.Position;

  gluDeleteQuadric(Quadric);  // �������� ������� ������� �������
  glDisable(GL_DEPTH_TEST);// ���������� ����� �������
  //Timer1.Enabled:= true;
end;

procedure TForm2.PrepareImage(bmap: string);
type
  PPixelArray = ^TPixelArray;
  TPixelArray = array [0..0] of Byte;
var
  Bitmap : TBitmap;
  Data, DataA : PPixelArray;
  BMInfo : TBitmapInfo;
  I, ImageSize : Integer;
  Temp : Byte;
  MemDC : HDC;
begin
  Bitmap := TBitmap.Create;
  Bitmap.LoadFromResourceName(HInstance,'Bitmap_1');

  with BMinfo.bmiHeader do
  begin
    FillChar (BMInfo, SizeOf(BMInfo), 0);
    biSize := sizeof (TBitmapInfoHeader);
    biBitCount := 24;
    biWidth := Bitmap.Width;
    biHeight := Bitmap.Height;
    ImageSize := biWidth * biHeight;
    biPlanes := 1;
    biCompression := BI_RGB;
    MemDC := CreateCompatibleDC (0);
    GetMem (Data, ImageSize * 3);
    GetMem (DataA, ImageSize * 4);
    try
    GetDIBits (MemDC, Bitmap.Handle, 0, biHeight, Data, BMInfo, DIB_RGB_COLORS);
    For I := 0 to ImageSize - 1 do
    begin
      Temp := Data [I * 3];
      Data [I * 3] := Data [I * 3 + 2];
      Data [I * 3 + 2] := Temp;
    end;

    For I := 0 to ImageSize - 1 do
    begin
      DataA [I * 4] := Data [I * 3];
      DataA [I * 4 + 1] := Data [I * 3 + 1];
      DataA [I * 4 + 2] := Data [I * 3 + 2];
      If (Data [I * 3 + 2] > 50) and (Data [I * 3 + 1] < 200) and  (Data [I * 3] < 200)
      then DataA [I * 4 + 3] := 127
      else
      DataA [I * 4 + 3] := 255;
    end;

    glTexImage2d(GL_TEXTURE_2D, 0, 3, biWidth,
                   biHeight, 0, GL_RGBA, GL_UNSIGNED_BYTE, DataA);
    finally
      FreeMem (Data);
      FreeMem (DataA);
      DeleteDC (MemDC);
      Bitmap.Free;
    end;
  end;
end;

procedure TForm2.ORB1;
type
  Tglobal_ambient  = Array[0..3] of GLFloat;
var
  Quadric:GLUquadricObj; //���������� ������� ������� �������

  const
  global_ambient:Tglobal_ambient = (3,3,3,3);
begin
  // glLightModelfv(GL_LIGHT_MODEL_AMBIENT, @global_ambient);
  glNewList(orbit1,GL_COMPILE);
    glcolor3f(255,0,255);
    Risovanie_Orbit(orbita1);
  glEndList;

  glNewList(orbit2,GL_COMPILE);
    glcolor3f(0,255,0);
    Risovanie_Orbit(orbita2);
  glEndList;
  FormResize(nil);
 // gluDeleteQuadric(Quadric);  // �������� ������� ������� �������
  //glDisable(GL_DEPTH_TEST);// ���������� ����� �������
end;

end.
