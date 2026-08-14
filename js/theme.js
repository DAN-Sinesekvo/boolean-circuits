(function(){
  const STORAGE_KEY = 'boolean-expressions-theme';
  const root = document.documentElement;
  const preference = window.matchMedia('(prefers-color-scheme: dark)');
  let manualTheme = null;

  try{
    const stored = sessionStorage.getItem(STORAGE_KEY);
    if(stored==='light' || stored==='dark') manualTheme=stored;
  }catch(e){
    // Theme switching still works when storage is unavailable.
  }

  function browserTheme(){ return preference.matches ? 'dark' : 'light'; }

  function updateControl(theme){
    const control=document.getElementById('themeToggle');
    if(!control) return;
    const isDark=theme==='dark';
    control.setAttribute('aria-checked',String(isDark));
    control.setAttribute('aria-label',isDark ? 'Switch to light theme' : 'Switch to dark theme');
    control.title=isDark ? 'Use light theme' : 'Use dark theme';
  }

  function applyTheme(theme){
    root.dataset.theme=theme;
    updateControl(theme);
  }

  function setManualTheme(theme){
    manualTheme=theme;
    try{ sessionStorage.setItem(STORAGE_KEY,theme); }catch(e){}
    applyTheme(theme);
  }

  function toggleTheme(){
    setManualTheme(root.dataset.theme==='dark' ? 'light' : 'dark');
  }

  applyTheme(manualTheme || browserTheme());

  document.addEventListener('DOMContentLoaded',()=>{
    const control=document.getElementById('themeToggle');
    updateControl(root.dataset.theme);
    if(control) control.addEventListener('click',toggleTheme);
  });

  const onPreferenceChange=event=>{
    if(!manualTheme) applyTheme(event.matches ? 'dark' : 'light');
  };
  if(preference.addEventListener) preference.addEventListener('change',onPreferenceChange);
  else if(preference.addListener) preference.addListener(onPreferenceChange);

  window.themeController={toggle:toggleTheme,getTheme:()=>root.dataset.theme};
})();
