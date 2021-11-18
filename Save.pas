unit Save;

interface

uses
  Winapi.Windows, Winapi.Messages, System.SysUtils, System.Variants, System.Classes, Vcl.Graphics,
  Vcl.Controls, Vcl.Forms, Vcl.Dialogs, Vcl.ExtCtrls, Vcl.StdCtrls ;

type
  TForm5 = class(TForm)
    Button1: TButton;
    Button2: TButton;
    Label1: TLabel;
    Button3: TButton;
    procedure Button2Click(Sender: TObject);
    procedure Button2KeyDown(Sender: TObject; var Key: Word;
      Shift: TShiftState);
    procedure Button1Click(Sender: TObject);
    procedure Button3Click(Sender: TObject);

  private
    { Private declarations }
  public
    { Public declarations }
  end;

var
  Form5: TForm5;

implementation

uses SchDU_2, Animation3D, Settings, Autors,ParamOG;
{$R *.dfm}

procedure TForm5.Button1Click(Sender: TObject);
begin
  form1.Sohranenie;
  Application.Terminate;
end;

procedure TForm5.Button2Click(Sender: TObject);
begin
   if FileExists('Parametry.ini') then DeleteFile('Parametry.ini');
  Application.Terminate;
end;

procedure TForm5.Button2KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
 If Key = 27 then  form5.Close;
end;

procedure TForm5.Button3Click(Sender: TObject);
begin
  form5.Close;
end;

end.
