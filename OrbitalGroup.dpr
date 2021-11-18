program OrbitalGroup;

{$R *.dres}

uses
  Vcl.Forms,
  ParamOG in 'ParamOG.pas' {Form1},
  SchDU_2 in 'SchDU_2.pas',
  Animation3D in 'Animation3D.pas' {Form2},
  Settings in 'Settings.pas' {Form3},
  Autors in 'Autors.pas' {Form4},
  Save in 'Save.pas' {Form5},
  Vyhod in 'Vyhod.pas' {Form6},
  Nachalo in 'Nachalo.pas' {Form7};

{$R *.res}

begin
  Application.Initialize;
  Application.MainFormOnTaskbar := True;
  Application.CreateForm(TForm1, Form1);
  Application.CreateForm(TForm2, Form2);
  Application.CreateForm(TForm3, Form3);
  Application.CreateForm(TForm4, Form4);
  Application.CreateForm(TForm5, Form5);
  Application.CreateForm(TForm6, Form6);
  Application.CreateForm(TForm7, Form7);
  Application.Icon.LoadFromResourceName(HInstance,'Icon_1');
  Application.Run;
end.
