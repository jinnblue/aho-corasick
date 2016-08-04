{***************************************************************************}
{描 述：AC自动机Trie树                                                      }
{功 能：字符串多模匹配:用于分词、赃词过滤
{作 者：賓虎  2016.08                                                       }
{***************************************************************************}
unit AhoCorasick.Trie;

interface

uses
  System.Classes, System.Generics.Collections, System.Generics.Defaults, AhoCorasick.Interval;

type
  { 状态具有以下功能:
    转向函数: 状态S_Curr在输入C后跳转到S_Next,如果不存在这样的跳转,则转向失效函数;
    失效函数: S_Fail := Goto(Fail(S_Curr), C); S_Fail状态节点应具有以下特征:
    1.从该S_Fail向上直到S_Root所经历的输入字符,和S_Curr向上所经历的输入字符串完全相同;
    2.并且S_Fail应该是符合条件的节点脏哦能深度最大的一个;
    3.如果不存在满足条件1和2的节点,则S_Curr → S_Root;
    命中函数: 表示当FSM到达该节点时,待匹配词组中的所有词可能已完全匹配 }
  PSuccessNode = ^TSuccessNode;
  TSuccess = TArray<PSuccessNode>;
  TEmits = TArray<TEmit>;
  TState = class(TObject)
  private
    FDepth: Integer;    // 模式串的长度,也是该状态的深度
    FSuccNum: Integer;
    FSuccess: TSuccess; // 转向函数表
    FFailure: TState;   // 失效函数,如果无匹配,则跳转到此状态
    FEmits: TEmits;     // 只要该状态可达,则记录模式串
  public
    Idx: Integer;
    constructor Create(const ADepth: Integer);
    destructor Destroy; override;
    function AddEmit(const AKeyword: string): TEmit; overload;
    procedure AddEmit(const AEmits: TEmits); overload;
    function GotoLeaf(const AChar: Char): TState; // 转向函数(基于Success转移)
    function AddLeaf(const AChar: Char): TState;  // 添加一个状态到Success函数
    function IsWordHead: Boolean; inline;         // 是否为词头
    procedure QuickSort(const aCompare: IComparer<PSuccessNode>);

    property Success: TSuccess read FSuccess;
    property Failure: TState read FFailure write FFailure;
    property Depth: Integer read FDepth;
    property Emits: TEmits read FEmits; // 获取该节点代表的模式串(们)
  end;

  TSuccessNode = record
    Key: Char;
    State: TState;
  end;

  TTrie = class(TObject)
  private
    FFileName: string;         // 字典词库
    FRootState: TState;        // 根节点
    FEmits: TList<TEmit>;      // 匹配,单独状态节点可能重复,因此保存在列表中一起释放
    FParses: TList<TEmit>;     // 匹配结果(自释放)
    FTokens: TList<TToken>;    // 分词结果(自释放)
    FItlTree: TIntervalTree;   //
    FFailuresCreated: Boolean; // 是否建立了failure表
    FCaseInsensitive: Boolean; // 是否忽略大小写
    FAllowOverlaps: Boolean;   // 是否允许模式串在位置上前后重叠
    FOnleyWholeWord: Boolean;  // 是否只匹配完整单词

    function CreateFragment(aEmit: TEmit; aText: string; aLastCollectedPos: Integer): TToken;
    function CreateMatch(aEmit: TEmit; aText: string): TToken;
    procedure RemovePartialMatches(aSearch: string);
    procedure CreateFailures;
    procedure CheckFailuresCreated;
    procedure ClearParseResult;
    procedure CLearTokenResult;
    procedure StoreEmits(aPos: Integer; aCurrent: TState);
    class function NextState(aCurrent: TState; const AChar: Char): TState;
    class function GotoNext(aCurrent: TState; const AChar: Char): TState;
  public
    constructor Create;
    destructor Destroy; override;

    procedure CaseSensitive;
    procedure RemoveOverlaps;
    procedure OnlyWholeWords;

    procedure AddKeyword(const aKey: string);
    function Tokenize(const aText: string): TList<TToken>;
    function ParseText(const aText: string): TList<TEmit>; // 模式匹配,返回值由自身释放
    function Filter(aText: string): string;
    function HasBlackWord(const aText: string): Boolean;
    function LoadKeywordsFromFile(const aFileName: string): Boolean;
    function Init(const aFileName: string): Boolean;
    property RootState: TState read FRootState;
  end;

function SuccessNodeCompareOrd(const ALeft, ARight: PSuccessNode): Integer;

implementation

uses
  System.SysUtils, System.StrUtils, System.Character;

var
  U_CompareOrd: IComparer<PSuccessNode>;

function IsSkipChar(var AChar: Char; const aCaseInsensitive: Boolean): Boolean;
begin
  Result := not AChar.IsLetterOrDigit;
  if Result then
    Exit;
  if aCaseInsensitive then
    AChar := AChar.ToUpper;
end;

function SuccessNodeCompareOrd(const ALeft, ARight: PSuccessNode): Integer;
begin
  Result := Word(ALeft^.Key) - Word(ARight^.Key);
end;

{ TState }
constructor TState.Create(const ADepth: Integer);
begin
  inherited Create;

  FSuccNum := 0;
  FDepth := ADepth;
  Failure := nil;
  if FDepth = 0 then
    FFailure := Self;
end;

destructor TState.Destroy;
var
  LP: PSuccessNode;
begin
  for LP in FSuccess do
  begin
    LP.State.Free;
    Dispose(LP);
  end;
  SetLength(FSuccess, 0);
  SetLength(FEmits, 0);
  inherited;
end;

procedure TState.AddEmit(const AEmits: TEmits);
var
  LEmit: TEmit;
begin
  for LEmit in AEmits do
  begin
    SetLength(FEmits, Length(FEmits) + 1);
    FEmits[high(FEmits)] := LEmit;
  end;
end;

function TState.AddEmit(const AKeyword: string): TEmit;
begin
  SetLength(FEmits, Length(FEmits) + 1);
  Result := TEmit.Create(0, Length(AKeyword) - 1, AKeyword);
  FEmits[high(FEmits)] := Result;
end;

function TState.AddLeaf(const AChar: Char): TState;
var
  LP: PSuccessNode;
begin
  Result := GotoLeaf(AChar);
  if not Assigned(Result) then
  begin
    Result := TState.Create(FDepth + 1);

    New(LP);
    LP^.Key := AChar;
    LP^.State := Result;
    Inc(FSuccNum);
    SetLength(FSuccess, FSuccNum);
    FSuccess[FSuccNum - 1] := LP;

    QuickSort(U_CompareOrd);
  end;
end;

// @param AChar 希望按此字符转移
// @Result 转移结果
function TState.GotoLeaf(const AChar: Char): TState;
var
  L, R, C: Integer;
begin
  Result := nil;

  L := 0;
  R := FSuccNum - 1;
  while L <= R do
  begin
    C := (L + R) shr 1;
    if FSuccess[C]^.Key < AChar then
      L := C + 1
    else
    begin
      R := C - 1;
      if FSuccess[C]^.Key = AChar then
        Result := FSuccess[C]^.State;
    end;
  end;
end;

function TState.IsWordHead: Boolean;
begin
  Result := (FDepth = 1);
end;

procedure TState.QuickSort(const aCompare: IComparer<PSuccessNode>);
begin
  TArray.Sort<PSuccessNode>(FSuccess, aCompare);
end;

{ TTrie }
procedure TTrie.CaseSensitive;
begin
  FCaseInsensitive := False;
end;

procedure TTrie.RemoveOverlaps;
begin
  FAllowOverlaps := False;
end;

procedure TTrie.OnlyWholeWords;
begin
  FOnleyWholeWord := True;
end;

constructor TTrie.Create;
begin
  inherited Create;

  FCaseInsensitive := True;
  FAllowOverlaps := True;
  FOnleyWholeWord := False;

  FRootState := TState.Create(0);
  FFailuresCreated := False;

  FEmits := TList<TEmit>.Create;
  FParses := TList<TEmit>.Create;
  FTokens := TList<TToken>.Create;
end;

destructor TTrie.Destroy;
var
  I: Integer;
begin
  if Assigned(FRootState) then
    FRootState.Free;

  for I := 0 to FEmits.Count - 1 do
  begin
    FEmits[I].Free;
  end;
  FEmits.Free;

  ClearParseResult;
  FParses.Free;

  CLearTokenResult;
  FTokens.Free;

  inherited;
end;

procedure TTrie.ClearParseResult;
var
  I: Integer;
begin
  if FAllowOverlaps then
  begin
    for I := 0 to FParses.Count - 1 do
      FParses[I].Free;
  end
  else
  begin
    if Assigned(FItlTree) then
      FItlTree.Free;
  end;
  FParses.Clear;
end;

procedure TTrie.CLearTokenResult;
var
  I: Integer;
begin
  for I := 0 to FTokens.Count - 1 do
    FTokens[I].Free;

  FTokens.Clear;
end;

procedure TTrie.AddKeyword(const aKey: string);
var
  LKey: string;
  LCurr: TState;
  LChar: Char;
  LEmit: TEmit;
begin
  if Length(aKey) <= 0 then
    Exit;

  if FCaseInsensitive then
    LKey := aKey.ToUpper;

  LCurr := FRootState;
  for LChar in LKey do
  begin
    if not LChar.IsLetterOrDigit then
      Continue;

    LCurr := LCurr.AddLeaf(LChar);
  end;
  LEmit := LCurr.AddEmit(aKey);
  FEmits.Add(LEmit);
  FFailuresCreated := False;
end;

procedure TTrie.CheckFailuresCreated;
begin
  if not FFailuresCreated then
    CreateFailures;
end;

procedure TTrie.CreateFailures;
var
  LQueue: TQueue<TState>;
  LCurr, LNext: TState;
  LPreFail, LNextFail: TState;
  LP: PSuccessNode;
begin
  LQueue := TQueue<TState>.Create;
  try
    // 第一步，将深度为1的节点的failure设为根节点
    for LP in FRootState.Success do
    begin
      LCurr := LP^.State;
      LCurr.Failure := FRootState;
      LQueue.Enqueue(LCurr);
    end;

    // 第二步，为深度 > 1 的节点建立failure表，这是一个bfs
    while LQueue.Count > 0 do
    begin
      LCurr := LQueue.Dequeue;
      // 转向叶节点的Char集合
      for LP in LCurr.Success do
      begin
        LNext := LP^.State;
        LQueue.Enqueue(LNext);

        // 由下而上找到S_Fail
        LPreFail := LCurr.Failure;
        while NextState(LPreFail, LP^.Key) = nil do
          LPreFail := LPreFail.Failure;

        LNextFail := NextState(LPreFail, LP^.Key);
        LNext.Failure := LNextFail;
        // 将包含词加入命中表
        LNext.AddEmit(LNextFail.Emits)
      end;
    end;

    FFailuresCreated := True;
  finally
    LQueue.Free;
  end;
end;

procedure TTrie.StoreEmits(aPos: Integer; aCurrent: TState);
var
  LNew, LOld: TEmit;
begin
  for LOld in aCurrent.Emits do
  begin
    LNew := TEmit.Create(aPos - LOld.Size + 1, aPos, LOld.Keyword);
    FParses.Add(LNew);
  end;
end;

function TTrie.LoadKeywordsFromFile(const aFileName: string): Boolean;
var
  LLines: TStringList;
  LKey: string;
begin
  Result := False;
  if not FileExists(aFileName) then
    Exit;

  LLines := TStringList.Create;
  try
    LLines.LoadFromFile(aFileName, TEncoding.UTF8);
    for LKey in LLines do
    begin
      AddKeyword(Trim(LKey));
    end;
    Result := True;
  finally
    LLines.Free;
  end;
end;

function TTrie.Init(const aFileName: string): Boolean;
begin
  FFileName := aFileName;
  if LoadKeywordsFromFile(FFileName) then
    CreateFailures;

  Result := FFailuresCreated;
end;

class function TTrie.GotoNext(aCurrent: TState; const AChar: Char): TState;
begin
  Result := NextState(aCurrent, AChar); // 先按Success跳转
  while Result = nil do
  begin
    aCurrent := aCurrent.Failure;
    Result := NextState(aCurrent, AChar)
  end;
end;

class function TTrie.NextState(aCurrent: TState; const AChar: Char): TState;
begin
  Result := aCurrent.GotoLeaf(AChar);
  if (Result = nil) and (aCurrent.Depth = 0) then
    Result := aCurrent;
end;

function TTrie.CreateFragment(aEmit: TEmit; aText: string; aLastCollectedPos: Integer): TToken;
var
  LCount: Integer;
begin
  LCount := Length(aText) + 1;
  if Assigned(aEmit) then
    LCount := aEmit.GetStart;
  Dec(LCount, aLastCollectedPos);
  Result := TFragmentToken.Create(MidStr(aText, aLastCollectedPos, LCount));
end;

function TTrie.CreateMatch(aEmit: TEmit; aText: string): TToken;
begin
  Result := TMatchToken.Create(MidStr(aText, aEmit.GetStart, aEmit.Size), aEmit);
end;

function TTrie.Tokenize(const aText: string): TList<TToken>;
var
  LLastCollectedPos: Integer;
  LEmit: TEmit;
begin
  ClearParseResult;
  ParseText(aText);

  LLastCollectedPos := 1;
  for LEmit in FParses do
  begin
    if LEmit.GetStart - LLastCollectedPos > 0 then
      FTokens.Add(CreateFragment(LEmit, aText, LLastCollectedPos));
    FTokens.Add(CreateMatch(LEmit, aText));
    LLastCollectedPos := LEmit.GetEnd + 1;
  end;

  if Length(aText) - LLastCollectedPos > 0 then
    FTokens.Add(CreateFragment(nil, aText, LLastCollectedPos));
  Result := FTokens;
end;

function TTrie.ParseText(const aText: string): TList<TEmit>;
var
  I: Integer;
  LText: string;
  LChar: Char;
  LCurr: TState;
begin
  CheckFailuresCreated;
  ClearParseResult;

  if FCaseInsensitive then
    LText := aText.ToUpper;

  I := 0;
  LCurr := FRootState;
  for LChar in LText do
  begin
    Inc(I);
    if not LChar.IsLetterOrDigit then
      Continue;

    LCurr := GotoNext(LCurr, LChar);
    StoreEmits(I, LCurr);
  end;

  if FOnleyWholeWord then
    RemovePartialMatches(LText);

  if not FAllowOverlaps then
  begin
    FItlTree := TIntervalTree.Create(TList<TInterval>(FParses));
    FItlTree.RemoveOverlaps(TList<TInterval>(FParses));
  end;

  Result := FParses;
end;

function TTrie.Filter(aText: string): string;
var
  I, J, N, LStart: Integer;
  LText: string;
  LChar: Char;
  LCurr: TState;
begin
  CheckFailuresCreated;

  if FCaseInsensitive then
    LText := aText.ToUpper;

  N := 0;
  LCurr := FRootState;
  for I := 1 to Length(LText) do
  begin
    Inc(N);
    LChar := LText[I];
    if not LChar.IsLetterOrDigit then
    begin
      Continue;
    end;
    LCurr := GotoNext(LCurr, LChar);

    if LCurr.IsWordHead then
    begin
      N := 0;
    end;
    if Length(LCurr.Emits) > 0 then
    begin
      LStart := I - N;
      for J := LStart to I do
        aText[J] := '*';

      N := 0;
    end;
  end;
  Result := aText;
end;

function TTrie.HasBlackWord(const aText: string): Boolean;
var
  I: Integer;
  LChar: Char;
  LCurr: TState;
begin
  Result := False;
  CheckFailuresCreated;

  LCurr := FRootState;
  for I := 1 to Length(aText) do
  begin
    LChar := aText[I];
    if not LChar.IsLetterOrDigit then
      Continue;

    if FCaseInsensitive then
      LChar := LChar.ToUpper;

    LCurr := GotoNext(LCurr, LChar);
    if Length(LCurr.Emits) > 0 then
    begin
      Exit(True);
    end;
  end;
end;

procedure TTrie.RemovePartialMatches(aSearch: string);
var
  LSize: Integer;
  I: Integer;
  LEmit: TEmit;
begin
  LSize := Length(aSearch);
  for I := FParses.Count - 1 downto 0 do
  begin
    LEmit := FParses[I];
    if ((LEmit.GetStart = 1) or (not Char(aSearch[LEmit.GetStart - 1]).IsLetterOrDigit)) and
      ((LEmit.GetEnd = LSize) or (not Char(aSearch[LEmit.GetEnd + 1]).IsLetterOrDigit)) then
    begin
      Continue;
    end;

    FParses.Remove(LEmit);
    LEmit.Free;
  end;
end;

initialization
  U_CompareOrd := TComparer<PSuccessNode>.Construct(SuccessNodeCompareOrd);

finalization
  U_CompareOrd := nil;

end.
