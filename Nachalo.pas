unit Nachalo;

interface

uses
  Winapi.Windows, Winapi.Messages, System.SysUtils, System.Variants, System.Classes, Vcl.Graphics,
  Vcl.Controls, Vcl.Forms, Vcl.Dialogs, Vcl.StdCtrls, Vcl.ExtCtrls;

type
  TForm7 = class(TForm)
    Label1: TLabel;
    Timer1: TTimer;
    procedure Timer1Timer(Sender: TObject);
    procedure FormShow(Sender: TObject);

  private
    { Private declarations }
  public
    { Public declarations }
  end;

var
  Form7: TForm7;

implementation

{$R *.dfm}
uses Animation3D, Settings;


procedure TForm7.FormShow(Sender: TObject);
begin
  form7.Timer1.Enabled:=true;
end;

procedure TForm7.Timer1Timer(Sender: TObject);
begin
  if form7.AlphaBlendValue<>255 then

  form7.AlphaBlendValue:= form7.AlphaBlendValue+1
  else form7.Timer1.Enabled:=false;

end;

end.
