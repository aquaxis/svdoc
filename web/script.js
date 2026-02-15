/**
 * SystemVerilog入門書 Webビューワー
 * Markdownファイルの読み込み・パース・表示・目次自動生成
 */

// =============================================================================
// グローバル変数・設定
// =============================================================================

/** @type {Array<{file: string, title: string}>} チャプター一覧 */
const chapters = [
  { file: "chapter01.md", title: "第1章" },
  { file: "chapter02.md", title: "第2章" },
  { file: "chapter03.md", title: "第3章" },
  { file: "chapter04.md", title: "第4章" },
  { file: "chapter05.md", title: "第5章" },
  { file: "chapter06.md", title: "第6章" },
  { file: "chapter07.md", title: "第7章" },
  { file: "chapter08.md", title: "第8章" },
  { file: "chapter09.md", title: "第9章" },
  { file: "chapter10.md", title: "第10章" },
  { file: "chapter11.md", title: "第11章" },
  { file: "chapter12.md", title: "第12章" },
  { file: "chapter13.md", title: "第13章" },
  { file: "chapter14.md", title: "第14章" },
  { file: "chapter15.md", title: "第15章" },
  { file: "chapter16.md", title: "第16章" },
  { file: "chapter17.md", title: "第17章" },
  { file: "chapter18.md", title: "第18章" },
  { file: "appendix.md", title: "付録" }
];

/** @type {string} Markdownファイルのベースパス（web/からdocs/への相対パス） */
const DOCS_PATH = "../docs/";

/** @type {string} 画像ファイルのベースパス（web/からimages/への相対パス） */
const IMAGES_PATH = "../images/";

// =============================================================================
// marked.js 設定
// =============================================================================

/**
 * marked.jsの初期設定を行う。
 * highlight.jsによるシンタックスハイライトと画像パス変換を設定する。
 */
function configureMarked() {
  // カスタムレンダラーの作成
  const renderer = new marked.Renderer();

  // 画像パス変換: ../images/, ./images/, images/ をすべて正しい相対パスに変換
  const originalImage = renderer.image.bind(renderer);
  renderer.image = function (token) {
    let href = token.href || "";
    // 様々な画像パスパターンを正規化
    if (href.match(/^(\.\.\/|\.\/)?images\//)) {
      href = href.replace(/^(\.\.\/|\.\/)?images\//, IMAGES_PATH);
    }
    token.href = href;
    return originalImage(token);
  };

  // marked.jsのオプション設定
  marked.setOptions({
    renderer: renderer,
    highlight: function (code, lang) {
      if (lang && hljs.getLanguage(lang)) {
        try {
          return hljs.highlight(code, { language: lang }).value;
        } catch (e) {
          console.warn("highlight.js エラー:", e);
        }
      }
      // 言語が指定されていない場合は自動検出
      try {
        return hljs.highlightAuto(code).value;
      } catch (e) {
        console.warn("highlight.js 自動検出エラー:", e);
      }
      return code;
    },
    gfm: true,
    breaks: true
  });
}

// =============================================================================
// Markdown ファイル読み込み
// =============================================================================

/**
 * 全チャプターのMarkdownファイルを順番に読み込む。
 * 読み込めなかったファイルはスキップし、エラーをconsole.warnで表示する。
 * @returns {Promise<void>}
 */
async function loadAllChapters() {
  const contentEl = document.getElementById("content");
  const loadingEl = document.getElementById("loading");

  let loadedCount = 0;

  for (let i = 0; i < chapters.length; i++) {
    const chapter = chapters[i];
    try {
      const html = await loadChapter(chapter);
      if (html) {
        // 章番号を2桁ゼロ埋めで生成（appendixは特別扱い）
        const chapterId = chapter.file === "appendix.md"
          ? "appendix"
          : `chapter-${String(i + 1).padStart(2, "0")}`;

        // section要素で各章を囲む
        const section = document.createElement("section");
        section.id = chapterId;
        section.innerHTML = html;
        contentEl.appendChild(section);

        loadedCount++;
      }
    } catch (err) {
      console.warn(`チャプター読み込みエラー (${chapter.file}):`, err);
    }
  }

  // 読み込み完了後、ローディング表示を非表示にする
  if (loadingEl) {
    loadingEl.style.display = "none";
  }

  if (loadedCount === 0) {
    const noContent = document.createElement("p");
    noContent.textContent = "コンテンツの読み込みに失敗しました。ファイルが存在するか確認してください。";
    noContent.style.padding = "2rem";
    noContent.style.color = "#666";
    contentEl.appendChild(noContent);
  }
}

/**
 * 1つのチャプターのMarkdownファイルを読み込み、HTMLに変換する。
 * @param {{file: string, title: string}} chapter - チャプター情報
 * @returns {Promise<string|null>} 変換後のHTML文字列。読み込み失敗時はnull
 */
async function loadChapter(chapter) {
  const url = DOCS_PATH + chapter.file;

  try {
    const response = await fetch(url);
    if (!response.ok) {
      console.warn(`ファイル取得失敗: ${url} (status: ${response.status})`);
      return null;
    }

    const markdown = await response.text();
    const html = marked.parse(markdown);
    return html;
  } catch (err) {
    console.warn(`ファイル読み込みエラー: ${url}`, err);
    return null;
  }
}

// =============================================================================
// 目次(TOC) 自動生成
// =============================================================================

/**
 * 変換後のHTMLからh1, h2, h3要素を取得し、目次を自動生成する。
 * 各見出しにユニークなid属性を付与し、目次項目をTOCリストに追加する。
 */
function generateTOC() {
  const tocEl = document.getElementById("toc");
  const contentEl = document.getElementById("content");

  if (!tocEl || !contentEl) {
    console.warn("TOCまたはコンテンツ要素が見つかりません");
    return;
  }

  // 既存の目次をクリア
  tocEl.innerHTML = "";

  // h1, h2, h3要素を取得
  const headings = contentEl.querySelectorAll("h1, h2, h3");
  const idCounter = {};

  headings.forEach(function (heading) {
    // ユニークなidを生成（既にあればそのまま使用）
    if (!heading.id) {
      // 見出しテキストからidを生成
      let baseId = heading.textContent
        .trim()
        .toLowerCase()
        .replace(/\s+/g, "-")
        .replace(/[^\w\u3000-\u9fff\uf900-\ufaff\u4e00-\u9faf\-]/g, "");

      // 空のIDを防止
      if (!baseId) {
        baseId = "heading";
      }

      // 重複を避けるためカウンターを使用
      if (idCounter[baseId] === undefined) {
        idCounter[baseId] = 0;
        heading.id = baseId;
      } else {
        idCounter[baseId]++;
        heading.id = baseId + "-" + idCounter[baseId];
      }
    }

    // 目次項目を作成
    const li = document.createElement("li");
    const a = document.createElement("a");
    const tagName = heading.tagName.toLowerCase(); // h1, h2, h3

    li.className = "toc-" + tagName;
    a.href = "#" + heading.id;
    a.textContent = heading.textContent;

    // スムーズスクロール
    a.addEventListener("click", function (e) {
      e.preventDefault();
      const target = document.getElementById(heading.id);
      if (target) {
        target.scrollIntoView({ behavior: "smooth" });
        // URLハッシュを更新（ブラウザ履歴に追加）
        history.pushState(null, "", "#" + heading.id);
      }
      // モバイルではサイドバーを閉じる
      closeSidebar();
    });

    li.appendChild(a);
    tocEl.appendChild(li);
  });
}

// =============================================================================
// モバイルメニュー制御
// =============================================================================

/**
 * モバイルメニューのトグルボタンとオーバーレイのイベントリスナーを設定する。
 */
function setupMobileMenu() {
  const menuToggle = document.getElementById("menu-toggle");
  const sidebar = document.getElementById("sidebar");
  const overlay = document.getElementById("overlay");

  if (menuToggle && sidebar) {
    menuToggle.setAttribute("aria-expanded", "false");
    menuToggle.addEventListener("click", function () {
      sidebar.classList.toggle("active");
      const isActive = sidebar.classList.contains("active");
      menuToggle.setAttribute("aria-expanded", isActive);
      if (overlay) {
        overlay.classList.toggle("active");
      }
    });
  }

  if (overlay) {
    overlay.addEventListener("click", function () {
      closeSidebar();
    });
  }

  // Escapeキーでサイドバーを閉じる
  document.addEventListener("keydown", function (e) {
    if (e.key === "Escape") {
      closeSidebar();
      if (menuToggle) {
        menuToggle.setAttribute("aria-expanded", "false");
      }
    }
  });
}

/**
 * サイドバーとオーバーレイを閉じる。
 */
function closeSidebar() {
  const sidebar = document.getElementById("sidebar");
  const overlay = document.getElementById("overlay");
  const menuToggle = document.getElementById("menu-toggle");

  if (sidebar) {
    sidebar.classList.remove("active");
  }
  if (overlay) {
    overlay.classList.remove("active");
  }
  if (menuToggle) {
    menuToggle.setAttribute("aria-expanded", "false");
  }
}

// =============================================================================
// スクロール追従（目次ハイライト）
// =============================================================================

/**
 * スクロール位置に応じて現在表示中の見出しに対応する目次項目にactiveクラスを付与する。
 * IntersectionObserverを使用して実装する。
 */
function setupScrollSpy() {
  const tocEl = document.getElementById("toc");
  if (!tocEl) return;

  const contentEl = document.getElementById("content");
  if (!contentEl) return;

  const headings = contentEl.querySelectorAll("h1, h2, h3");
  if (headings.length === 0) return;

  // IntersectionObserverのコールバック
  const observerCallback = function (entries) {
    entries.forEach(function (entry) {
      if (entry.isIntersecting) {
        // 全TOCアイテムからactiveを除去
        const tocLinks = tocEl.querySelectorAll("a");
        tocLinks.forEach(function (link) {
          link.classList.remove("active");
        });

        // 対応するTOCアイテムにactiveを付与
        const escapedId = CSS.escape(entry.target.id);
        const activeLink = tocEl.querySelector('a[href="#' + escapedId + '"]');
        if (activeLink) {
          activeLink.classList.add("active");
        }
      }
    });
  };

  // IntersectionObserverのオプション
  const observerOptions = {
    root: null,
    rootMargin: "-10% 0px -80% 0px",
    threshold: 0
  };

  const observer = new IntersectionObserver(observerCallback, observerOptions);

  // 各見出し要素を監視
  headings.forEach(function (heading) {
    observer.observe(heading);
  });
}

// =============================================================================
// PDF出力（placeholder）
// =============================================================================

/**
 * PDF出力機能。
 * html2pdf.jsを使用してid="content"のmain要素全体をA4縦向きPDFに変換・ダウンロードする。
 * 出力中はボタンを無効化し、サイドバーを一時的に非表示にしてレイアウトを調整する。
 * @returns {Promise<void>}
 */
async function exportPDF() {
  const pdfBtn = document.getElementById("pdf-export");
  const sidebar = document.getElementById("sidebar");
  const contentEl = document.getElementById("content");

  if (!contentEl) {
    alert("コンテンツ要素が見つかりません。");
    return;
  }

  // ボタンを「出力中...」に変更しdisabled状態にする
  const originalBtnText = pdfBtn ? pdfBtn.textContent : "";
  if (pdfBtn) {
    pdfBtn.textContent = "出力中...";
    pdfBtn.disabled = true;
  }

  // PDF出力前の一時的なスタイル調整（元の値を保存）
  const originalSidebarDisplay = sidebar ? sidebar.style.display : "";
  const originalContentMarginLeft = contentEl.style.marginLeft;

  try {
    // サイドバーを一時的に非表示にする
    if (sidebar) {
      sidebar.style.display = "none";
    }
    // コンテンツの左マージンを0にする
    contentEl.style.marginLeft = "0";

    // html2pdf.jsのオプション設定
    const opt = {
      margin:       10,
      filename:     "SystemVerilog_入門書.pdf",
      image:        { type: "jpeg", quality: 0.98 },
      html2canvas:  { scale: 2, useCORS: true, letterRendering: true },
      jsPDF:        { unit: "mm", format: "a4", orientation: "portrait" },
      pagebreak:    { mode: "avoid-all", before: ".page-break" }
    };

    // html2pdf.jsでPDFを生成・ダウンロード
    await html2pdf().set(opt).from(contentEl).save();

  } catch (err) {
    console.error("PDF出力エラー:", err);
    alert("PDF出力中にエラーが発生しました: " + err.message);
  } finally {
    // スタイルを元に戻す
    if (sidebar) {
      sidebar.style.display = originalSidebarDisplay;
    }
    contentEl.style.marginLeft = originalContentMarginLeft;

    // ボタンを元に戻す
    if (pdfBtn) {
      pdfBtn.textContent = originalBtnText;
      pdfBtn.disabled = false;
    }
  }
}

// =============================================================================
// 初期化
// =============================================================================

/**
 * アプリケーションの初期化を行う。
 * DOMContentLoaded時に呼び出される。
 * 1. marked.jsの設定（highlight.jsによるシンタックスハイライト含む）
 * 2. モバイルメニューの設定
 * 3. PDF出力ボタンの設定
 * 4. 全チャプターの読み込み（marked.jsのhighlight機能でハイライト済み）
 * 5. 目次の生成
 * 6. スクロール追従の設定
 * @returns {Promise<void>}
 */
async function init() {
  try {
    // スキップリンクの追加（アクセシビリティ）
    const skipLink = document.createElement("a");
    skipLink.href = "#content";
    skipLink.className = "skip-link";
    skipLink.textContent = "本文へスキップ";
    skipLink.style.cssText = "position:fixed;top:-100px;left:0;background:#1a237e;color:#fff;padding:8px 16px;z-index:10000;transition:top 0.3s;";
    skipLink.addEventListener("focus", function() { this.style.top = "0"; });
    skipLink.addEventListener("blur", function() { this.style.top = "-100px"; });
    document.body.insertBefore(skipLink, document.body.firstChild);

    // marked.jsの設定
    configureMarked();

    // モバイルメニューの設定
    setupMobileMenu();

    // PDF出力ボタンのイベントリスナー設定
    const pdfBtn = document.getElementById("pdf-export");
    if (pdfBtn) {
      pdfBtn.addEventListener("click", exportPDF);
    }

    // 全チャプターのMarkdownファイルを読み込み
    await loadAllChapters();

    // 目次の自動生成
    generateTOC();

    // スクロール追従の設定
    setupScrollSpy();

    // 初期URLハッシュ対応
    if (window.location.hash) {
      const targetId = decodeURIComponent(window.location.hash.substring(1));
      const target = document.getElementById(targetId);
      if (target) {
        setTimeout(function() {
          target.scrollIntoView({ behavior: "smooth" });
        }, 500);
      }
    }

  } catch (err) {
    console.error("初期化エラー:", err);
    // ローディング表示を非表示にする
    const loadingEl = document.getElementById("loading");
    if (loadingEl) {
      loadingEl.textContent = "エラーが発生しました。ページを再読み込みしてください。";
    }
  }
}

// DOMContentLoaded時に初期化を実行
document.addEventListener("DOMContentLoaded", init);
