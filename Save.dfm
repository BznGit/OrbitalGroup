object Form5: TForm5
  Left = 0
  Top = 0
  BorderStyle = bsNone
  Caption = 'Form5'
  ClientHeight = 158
  ClientWidth = 780
  Color = clBackground
  Font.Charset = DEFAULT_CHARSET
  Font.Color = clWindowText
  Font.Height = -13
  Font.Name = 'Tahoma'
  Font.Style = []
  OldCreateOrder = False
  Position = poScreenCenter
  PixelsPerInch = 120
  TextHeight = 16
  object Label1: TLabel
    Left = 176
    Top = 40
    Width = 432
    Height = 18
    Caption = #1057#1086#1093#1088#1072#1085#1080#1090#1100' '#1079#1072#1076#1072#1085#1085#1099#1077' '#1087#1072#1088#1072#1084#1077#1090#1088#1099' '#1086#1088#1073#1080#1090' '#1080' '#1086#1090#1086#1073#1088#1072#1078#1077#1085#1080#1103'?'
    Font.Charset = DEFAULT_CHARSET
    Font.Color = clAqua
    Font.Height = -15
    Font.Name = 'Tahoma'
    Font.Style = [fsBold]
    ParentFont = False
  end
  object Button1: TButton
    Left = 235
    Top = 72
    Width = 104
    Height = 33
    Caption = #1044#1072
    TabOrder = 0
    OnClick = Button1Click
  end
  object Button2: TButton
    Left = 345
    Top = 72
    Width = 104
    Height = 33
    Caption = #1053#1077#1090
    TabOrder = 1
    OnClick = Button2Click
    OnKeyDown = Button2KeyDown
  end
  object Button3: TButton
    Left = 455
    Top = 72
    Width = 104
    Height = 33
    Caption = #1054#1090#1084#1077#1085#1072
    TabOrder = 2
    OnClick = Button3Click
  end
end
