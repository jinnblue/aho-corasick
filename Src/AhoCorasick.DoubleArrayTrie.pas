{***************************************************************************}
{描 述：AC自动机结合双数组Trie树; 只适合做脏词过滤;                         }
{功 能：极速字符串多模式匹配,占用空间相对ACTrie较大,词组多时初始化耗时长
{作 者：賓虎  2016.08                                                       }
{***************************************************************************}
unit AhoCorasick.DoubleArrayTrie;

interface

uses
  System.Classes, System.Generics.Collections, AhoCorasick.Trie;

type
  {Base数组: 1.每个元素表示一个Trie节点,即一个状态,初始状态S_Root设置为 FBase[1] = 1;
             2.如果某个状态x为一个完整的词,则 FBase [x]  设置为负数(-FBase [x] );
   Check数组: 1.每个元素表示某个状态的前驱状态; S_Root: FCheck[0] = 0;
              2.如果某个状态y为一个完整的词,且该词不为其他词的前缀,则 FCheck [y]  设置为 -FCheck [y] ;
   Fail数组: 失败函数映射;
   关系条件: <S_Curr_Idx:当前状态的下标, S_Next_Idx:转移状态的下标, Char: 输入字符的数值>;
             1.FBase[S_Curr_Idx] + FMap[Char] = S_Next_Idx;
             2.FCheck[S_Next_Idx] = S_Curr_Idx;}
  TDoubleArrayTrie = class(TObject)
  private type
    TDAState = Integer;
  private const
    ROOT = 0;
    INVALID_MAP = 0;
  private
    FTrie: TTrie;
    FBase: TArray<Integer>;
    FCheck: TArray<Integer>;
    FFail: TArray<Integer>;
    FSize: Integer;
    FInited: Boolean;
    FFileName: string;
    FCaseInsensitive: Boolean;  //是否忽略大小写

    procedure ReSize(const aSize: Integer);
    function MapWords: Integer;
    procedure CalcArrayValue(const aBaseStart: Integer);
    function NextState(aCurrent: TDAState; const ACode: Word): TDAState;
    function GotoNext(aCurrent: TDAState; const AKey: Word): TDAState;
  public
    constructor Create();
    destructor Destroy; override;

    procedure CaseSensitive;
    function Init(const aFileName: string): Boolean;
    function Filter(aText: string): string;
    function HasBlackWord(const aText: string): Boolean;
  end;

function SuccessNodeCompareMapCode(const ALeft, ARight: PSuccessNode): Integer;
  
implementation

uses
  System.Generics.Defaults, System.SysUtils, System.Character;

var
  U_MAP: array[Word] of Word;
  U_Compare: IComparer<PSuccessNode>;

function SuccessNodeCompareMapCode(const ALeft, ARight: PSuccessNode): Integer;
begin
  Result := U_MAP[Word(ALeft.Key)] - U_MAP[Word(ARight.Key)];
end;
  
{ TDoubleArrayTrie }
constructor TDoubleArrayTrie.Create;
begin
  inherited Create;
  FInited := False;
  FCaseInsensitive := True;
end;

destructor TDoubleArrayTrie.Destroy;
begin
  ReSize(0);
  inherited;
end;

procedure TDoubleArrayTrie.ReSize(const aSize: Integer);
begin
  SetLength(FBase, aSize);
  SetLength(FCheck, aSize);
  SetLength(FFail, aSize);
  FSize := aSize;
end;

function TDoubleArrayTrie.MapWords: Integer;
var
  I: Integer;
  LCode: Word;
  LQueue: TQueue<TState>;
  LP: PSuccessNode;
  LCurr, LNext: TState;
begin
  for I := Low(U_MAP) to High(U_MAP) do
  begin
    U_MAP[I] := INVALID_MAP;
  end;
  
  FSize := 2;
  LCode := INVALID_MAP;   //字符起始编码

  LQueue := TQueue<TState>.Create;
  try
    for LP in FTrie.RootState.Success do
    begin
      LQueue.Enqueue(LP.State);

      if U_MAP[Word(LP.Key)] = INVALID_MAP then
      begin
        Inc(LCode);
        U_MAP[Word(LP.Key)] := LCode;
        //获取深度=1的宽度
        Inc(FSize);
      end;
    end;      
    Result := FSize;

    //编码深度>1的节点
    while LQueue.Count > 0 do
    begin
      LCurr := LQueue.Dequeue;
      for LP in LCurr.Success do
      begin
        LNext := LP.State;
        LQueue.Enqueue(LNext);

        if U_MAP[Word(LP.Key)] = INVALID_MAP then
        begin
          Inc(LCode);
          U_MAP[Word(LP.Key)] := LCode;
        end;
        Inc(FSize);
      end;
    end;

    ReSize(FSize);

    FBase[ROOT] := 1;
    FCheck[ROOT] := ROOT;
    FFail[ROOT] := ROOT;
    FTrie.RootState.Idx := ROOT;
  finally
    LQueue.Free;
  end;
end;

procedure TDoubleArrayTrie.CalcArrayValue(const aBaseStart: Integer);
var
  LQueue: TQueue<TState>;
  LP: PSuccessNode;
  LCurr, LNext: TDAState;
  LCurr_S, LNext_S: TState;
  LIdx, LBase, LOK: Integer;
begin
  LQueue := TQueue<TState>.Create;
  try
{计算FCheck数组的值}  
    //深度=1的节点
    for LP in FTrie.RootState.Success do
    begin
      LCurr_S := LP.State;
      LQueue.Enqueue(LCurr_S);

      LCurr := FBase[ROOT] + U_MAP[Word(LP.Key)];
      if Length(LCurr_S.Emits) > 0 then
        FCheck[LCurr] := -ROOT
      else
        FCheck[LCurr] := ROOT;
      FFail[LCurr] := ROOT;
      LCurr_S.Idx := LCurr;
    end;

    //深度>1的节点
    while LQueue.Count > 0 do
    begin 
      LCurr_S := LQueue.Dequeue;
      LCurr := LCurr_S.Idx;
      if Length(LCurr_S.Success) = 0 then
        Continue;

      TArray.Sort<PSuccessNode>(LCurr_S.Success, U_Compare);
      if FBase[LCurr] = 0 then
      begin
        LIdx := aBaseStart;
        repeat      
          LOK := 0;
          LBase := LIdx - U_MAP[Word(LCurr_S.Success[0].Key)];
          for LP in LCurr_S.Success do
          begin
            LNext := LBase + U_MAP[Word(LP.Key)];
            if LNext >= FSize then
              ReSize(LNext + 1);
            LOK := LOK or FCheck[LNext] or FBase[LNext];
            if LOK <> 0 then
              Break;
          end;

          Inc(LIdx);
        until (LOK = 0);

        FBase[LCurr] := LBase;
      end;
      
      for LP in LCurr_S.Success do
      begin
        LNext_S := LP.State;
        LQueue.Enqueue(LNext_S);
        
        LNext := Abs(FBase[LCurr]) + U_MAP[Word(LP.Key)];
        if Length(LNext_S.Emits) > 0 then
          FCheck[LNext] := -LCurr
        else
          FCheck[LNext] := LCurr;
        LNext_S.Idx := LNext;
      end;
    end;

{计算FFail数组的值}
    for LP in FTrie.RootState.Success do
    begin
      LQueue.Enqueue(LP.State);
    end;

    while LQueue.Count > 0 do
    begin 
      LCurr_S := LQueue.Dequeue;
      for LP in LCurr_S.Success do
      begin
        LNext_S := LP.State;
        LQueue.Enqueue(LNext_S);
        
        LNext := LNext_S.Idx;
        FFail[LNext] := LNext_S.Failure.Idx;
      end;
    end;

    FInited := True;
  finally
    LQueue.Free;
  end;
end;

procedure TDoubleArrayTrie.CaseSensitive;
begin
  FCaseInsensitive := False;
end;

function TDoubleArrayTrie.Init(const aFileName: string): Boolean;
var
  LStart: Integer;
begin
  FFileName := aFileName;
  FTrie := TTrie.Create;
  try
    if FTrie.Init(FFileName) then
    begin
      LStart := MapWords;
      CalcArrayValue(LStart);
    end;
    Result := FInited;
  finally
    FTrie.Free;
  end;
end;

function TDoubleArrayTrie.NextState(aCurrent: TDAState; const ACode: Word): TDAState;
begin
  Result := Abs(FBase[aCurrent]) + ACode;
  if Abs(FCheck[Result]) <> aCurrent then
    Result := -1;
    
  if (Result = -1) and (aCurrent = ROOT) then
    Result := ROOT;
end;

function TDoubleArrayTrie.GotoNext(aCurrent: TDAState; const AKey: Word): TDAState;
begin
  Result := NextState(aCurrent, U_Map[AKey]); // 先按Success跳转
  while Result = -1 do
  begin
    aCurrent := FFail[aCurrent];
    Result := NextState(aCurrent, U_Map[AKey])
  end;
end;

function TDoubleArrayTrie.Filter(aText: string): string;
var
  I, J, N, LStart: Integer;
  LText: string;
  LChar: Char;
  LCurr: TDAState;
begin
  if not FInited then
    Init(FFileName);

  if FCaseInsensitive then
    LText := aText.ToUpper;
  
  N := 0;
  LCurr := ROOT;
  for I := 1 to Length(LText) do
  begin
    Inc(N);
    LChar := LText[I];
    if not LChar.IsLetterOrDigit then
    begin
      Continue;
    end;
    LCurr := GotoNext(LCurr, Word(LChar));

    if Abs(FCheck[LCurr]) = ROOT then
    begin
      N := 0;
    end;
    if FCheck[LCurr] < 0 then
    begin
      LStart := I - N;
      for J := LStart to I do
        aText[J] := '*';

      N := 0;
    end;
  end;
  Result := aText;
end;

function TDoubleArrayTrie.HasBlackWord(const aText: string): Boolean;
var
  I: Integer;
  LChar: Char;
  LCurr: TDAState;
begin
  Result := False;
  if not FInited then
    Init(FFileName);

  LCurr := ROOT;
  for I := 1 to Length(aText) do
  begin
    LChar := aText[I];
    if LChar.IsPunctuation then
      Continue;

    if FCaseInsensitive then
      LChar := LChar.ToUpper;

    LCurr := GotoNext(LCurr, Word(LChar));
    if FCheck[LCurr] < 0 then
    begin
      Exit(True);
    end;
  end;
end;


initialization
  U_Compare := TComparer<PSuccessNode>.Construct(SuccessNodeCompareMapCode);

end.
