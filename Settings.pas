unit Settings;

interface

uses
  Winapi.Windows, Winapi.Messages, System.SysUtils, System.Variants, System.Classes, Vcl.Graphics,
  Vcl.Controls, Vcl.Forms, Vcl.Dialogs, Vcl.ComCtrls, Vcl.StdCtrls, ParamOG, Animation3D, Autors;

type
  TForm3 = class(TForm)
    PageControl1: TPageControl;
    TabSheet1: TTabSheet;
    TabSheet2: TTabSheet;
    TabSheet3: TTabSheet;
    GroupBox2: TGroupBox;
    Label4: TLabel;
    Label5: TLabel;
    Label6: TLabel;
    Edit4: TEdit;
    Edit5: TEdit;
    Edit6: TEdit;
    Label1: TLabel;
    Edit1: TEdit;
    Label2: TLabel;
    Edit2: TEdit;
    GroupBox3: TGroupBox;
    Label11: TLabel;
    Label12: TLabel;
    Label13: TLabel;
    Label14: TLabel;
    Label15: TLabel;
    Edit11: TEdit;
    Edit12: TEdit;
    Edit13: TEdit;
    Edit14: TEdit;
    Edit15: TEdit;
    Button1: TButton;
    Button2: TButton;
    GroupBox1: TGroupBox;
    Label7: TLabel;
    Edit7: TEdit;
    UpDown1: TUpDown;
    Label3: TLabel;
    Label8: TLabel;
    procedure UpDown1Click(Sender: TObject; Button: TUDBtnType);
    procedure Button1Click(Sender: TObject);
    procedure Button2Click(Sender: TObject);
    procedure Edit4KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit5KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit6KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit1KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit2KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit11KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit12KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit13KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit14KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure Edit15KeyDown(Sender: TObject; var Key: Word; Shift: TShiftState);
    procedure UpDown1Changing(Sender: TObject; var AllowChange: Boolean);
    procedure FormCreate(Sender: TObject);
    procedure Edit4Change(Sender: TObject);
    procedure Edit5Change(Sender: TObject);
    procedure Edit6Change(Sender: TObject);
    procedure Edit1Change(Sender: TObject);
    procedure Edit2Change(Sender: TObject);
    procedure Edit11Change(Sender: TObject);
    procedure Edit12Change(Sender: TObject);
    procedure Edit13Change(Sender: TObject);
    procedure Edit14Change(Sender: TObject);
    procedure Edit15Change(Sender: TObject);


  private
    { Private declarations }
  public
    { Public declarations }
  end;

var
  Form3: TForm3;

implementation

{$R *.dfm}

procedure TForm3.Button1Click(Sender: TObject);
begin
  form1.Pereschet;
  form3.Close;
    vremya:=0;
    k1:=0;
    k2:=0;
end;

procedure TForm3.Button2Click(Sender: TObject);
begin
  form3.Close;
end;

procedure TForm3.Edit11Change(Sender: TObject);
begin
  zamena:=true;
  form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit11KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
    form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.Edit12Change(Sender: TObject);
begin
  zamena:=true;
  form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit12KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
    form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.Edit13Change(Sender: TObject);
begin
zamena:=true;
form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit13KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
    form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.Edit14Change(Sender: TObject);
begin
zamena:=true;
form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit14KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
    form1.Pereschet;
    form3.Close;

  end;
end;

procedure TForm3.Edit15Change(Sender: TObject);
begin
zamena:=true;
form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit15KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
     form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.Edit1Change(Sender: TObject);
begin
zamena:=true;
form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit1KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
     form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.Edit2Change(Sender: TObject);
begin
zamena:=true;
form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit2KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
     form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.Edit4Change(Sender: TObject);
begin
  zamena:=true;
  form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit4KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
    form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.Edit5Change(Sender: TObject);
begin
zamena:=true;
form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit5KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
    form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.Edit6Change(Sender: TObject);
begin
zamena:=true;
form2.Button8.Enabled:=true;
end;

procedure TForm3.Edit6KeyDown(Sender: TObject; var Key: Word;
  Shift: TShiftState);
begin
  If Key =vk_return then
  begin
    form1.Pereschet;
    form3.Close;
  end;
end;

procedure TForm3.FormCreate(Sender: TObject);
begin
  edit7.Text:=Inttostr(klv);
end;

procedure TForm3.UpDown1Changing(Sender: TObject; var AllowChange: Boolean);
begin
  klv:=form3.UpDown1.Position;
  edit7.Text:=Inttostr(klv);
end;

procedure TForm3.UpDown1Click(Sender: TObject; Button: TUDBtnType);
begin
  klv:=form3.UpDown1.Position;
  edit7.Text:=Inttostr(klv);
end;

end.
